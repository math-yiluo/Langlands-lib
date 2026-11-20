import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Automorphic.CuspidalWhittaker.PlaceWhittaker
import Langlands.Automorphic.PlaceComponentExistence
import Langlands.Global.Factors.IsobaricArchimedeanQuotients
import Langlands.Representation.Archimedean.RealLeviChartIntegrable
import Langlands.Representation.Archimedean.RealLeviLanglandsQuotient
import Langlands.Representation.Archimedean.RealLeviParabolicIntegration
import Langlands.Representation.Archimedean.RealStandardNontrivialProof
import Langlands.Representation.Archimedean.StandardQuotientFactorization

/-!
# The prescribed isobaric constituent at a real place

This reduction supplies the real-place data from the real generic standard
parameter theorem, tied real standard irreducibility, and transfer of a
specified irreducible quotient under reordering. It constructs the quotient of
the sorted concatenation and retains that same quotient in the original order.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct Matrix.Norms.Operator

namespace Langlands.Global

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Archimedean Langlands.Automorphic
open LocalFactor.Archimedean (RealBlock realRank)

universe u

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}

local notation "Standard(" n ", " ds ")" => realStandardKFinite n ds

/-- An irreducible quotient of a real standard module occurs as a subquotient of
the standard module obtained by permuting its blocks. -/
def RealStandardQuotientReorderingStatement : Prop :=
  ∀ (n : ℕ) (ds xs : List RealBlock), realRank ds = n → ds.Perm xs →
    ∀ (R : Submodule ℂ Standard(n, ds))
      (hR : IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) R),
      IsIrreducibleGKModule ((realStandardRep n ds).quotient R hR.1)
        (RealLeviDuality.quotLie (realStandardLie n ds) R hR.2) →
      ∃ (W : Submodule ℂ Standard(n, xs))
        (hW : IsGKSubmodule (realStandardRep n xs) (realStandardLie n xs) W)
        (q : W →ₗ[ℂ] (Standard(n, ds) ⧸ R)),
        IsGKSubquotientMap ((realStandardRep n ds).quotient R hR.1)
          (RealLeviDuality.quotLie (realStandardLie n ds) R hR.2) hW q

/-- The supplied cuspidal family has irreducible standard parameters at `v`.
The ordered concatenation has an irreducible quotient that occurs as a
subquotient of the standard module of the concatenation in the supplied order. -/
def HasRealIsobaricPlaceQuotient (T : ∀ i, CuspidalOperatorRealization F (m i))
    (v : RP) : Prop :=
  ∃ (ds : Fin k → List RealBlock) (es : List RealBlock),
    (∀ i, (T i).realization.HasRealPlaceParameter v (ds i) ∧
      IsIrreducibleGKModule (realStandardRep (m i + 1) (ds i))
        (realStandardLie (m i + 1) (ds i))) ∧
    es.Perm (List.ofFn ds).flatten ∧ realRank es = r + 1 ∧ IsRealLanglandsOrdered es ∧
    ∃ (R : Submodule ℂ Standard(r + 1, es))
      (hR : IsGKSubmodule (realStandardRep (r + 1) es) (realStandardLie (r + 1) es) R),
      IsIrreducibleGKModule ((realStandardRep (r + 1) es).quotient R hR.1)
        (RealLeviDuality.quotLie (realStandardLie (r + 1) es) R hR.2) ∧
      let xs := (List.ofFn ds).flatten
      ∃ (W : Submodule ℂ Standard(r + 1, xs))
        (hW : IsGKSubmodule (realStandardRep (r + 1) xs) (realStandardLie (r + 1) xs) W)
        (q : W →ₗ[ℂ] (Standard(r + 1, es) ⧸ R)),
        IsGKSubquotientMap ((realStandardRep (r + 1) es).quotient R hR.1)
          (RealLeviDuality.quotLie (realStandardLie (r + 1) es) R hR.2) hW q

private theorem irreducible_realStandard_of_injective {n : ℕ} {ds : List RealBlock}
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
    {A : Standard(n, ds) →ₗ[ℂ] V} (hA : IsRealStandardIntertwiner n ρ π ds A)
    (hinj : Function.Injective A) (hirr : IsIrreducibleGKModule ρ π)
    (hn : realRank ds = n) :
    IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) := by
  refine ⟨realStandardNontrivial n ds hn, fun W hK hL => ?_⟩
  have hmap := hirr.2 (W.map A)
    (fun k _ ⟨f, hf, h⟩ => ⟨_, hK k f hf, by rw [← h, hA.map_realStandardRep]⟩)
    (fun X _ ⟨f, hf, h⟩ => ⟨_, hL X f hf, by rw [← h, hA.map_realStandardLie]⟩)
  rcases hmap with h | h
  · left
    apply Submodule.map_injective_of_injective hinj
    rwa [Submodule.map_bot]
  · right
    rw [eq_top_iff]
    intro f _
    have hf : A f ∈ W.map A := h.symm ▸ Submodule.mem_top
    obtain ⟨g, hg, hgf⟩ := hf
    rwa [← hinj hgf]

/-- The real local construction, with its three representation-theoretic inputs. -/
theorem hasRealIsobaricPlaceQuotient_of
    (hparam : RealGenericStandardParameterStatement.{u})
    (htied : RealTemperedStandardIrreducibleStatement)
    (hpermute : RealStandardQuotientReorderingStatement)
    (hm : ∑ i, (m i + 1) = r + 1) (T : ∀ i, CuspidalOperatorRealization F (m i))
    (v : RP) : HasRealIsobaricPlaceQuotient (r := r) T v := by
  have hlocal (i : Fin k) : ∃ ds,
      (T i).realization.HasRealPlaceParameter v ds ∧
        IsIrreducibleGKModule (realStandardRep (m i + 1) ds)
          (realStandardLie (m i + 1) ds) := by
    obtain ⟨V, _, _, ρ, π, ι, hι, hρ, hπ, hgk, hirr, hadm, hgen⟩ :=
      (cuspidalArchimedeanGenericComponentBridge cuspidalArchimedeanIrreducibleAdmissibleComponent
        cuspidalArchimedeanWhittakerFunctional F (m i) (T i)).1 v
    obtain ⟨ds, hds⟩ := hparam (m i + 1) V ρ π hgk hirr hadm hgen
    have hplace := OperatorRealization.hasRealPlaceParameter_of_component hι hρ hπ hds
    obtain ⟨hn, A, hAinj, hA⟩ := (hasRealStandardParameter_iff _ ρ π ds).mp hds
    exact ⟨ds, hplace, irreducible_realStandard_of_injective hA hAinj hirr hn⟩
  choose ds hd using hlocal
  have hsum : ∑ i, realRank (ds i) = r + 1 :=
    (Finset.sum_congr rfl fun i _ => (hd i).1.1).trans hm
  obtain ⟨es, hes, hn, ho⟩ :=
    LocalFactor.Archimedean.exists_ordered_realBlock_concatenation ds hsum
  have ho' := LocalFactor.Archimedean.isRealLanglandsOrdered_iff.mp ho
  obtain ⟨R, hR, hproper, hmax⟩ :=
    realLeviLanglandsQuotient realLeviChartIntegrable realLeviParabolicIntegration htied
      (r + 1) es hn ho'
  have hJ := isIrreducibleGKModule_quotient_of_largest hR hproper hmax
  exact ⟨ds, es, hd, hes, hn, ho', R, hR, hJ, hpermute (r + 1) es _ hn hes R hR hJ⟩

end Langlands.Global
