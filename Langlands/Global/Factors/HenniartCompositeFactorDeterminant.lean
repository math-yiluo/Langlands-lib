import Langlands.Global.Factors.HenniartCompositeMapStatement
import Langlands.Global.Factors.CompletionReciprocityTransport
import Langlands.Global.Factors.HenniartCompositeFactorWeil
import Langlands.Global.Factors.HenniartCompositeFactorCentral

/-!
# The determinant clause for Henniart's composite map
-/

noncomputable section

universe u uF uK uW uP uV uE

namespace Langlands.Global

open NumberField Langlands.Weil.Local Langlands.Global.CompletionPadic
open Langlands.VirtualRepresentation

section Transport

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)
  {p : ℕ} [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
  (f : letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier)

/-- The local Weil map of `f : K ≅ F_v` preserves the integer degree. -/
theorem localDegreeInt_completionWeilEquiv (w : localWeilGroup K) :
    localDegreeInt (padicField v) (completionWeilEquiv v h K f w) = localDegreeInt K w := by
  subst h
  let _ := (padicFieldAt v rfl).algebra
  exact localDegreeInt_extensionWeilEquiv (padicFieldAt v rfl) K f.symm w

/-- Pullback of unitary supercuspidal classes from `F_v` to `K` turns a central
character `ω` into `ω ∘ f`. -/
theorem isUnitaryCentralCharacter_completionSupercuspidalLatticeEquiv
    (y : PadicSupercuspidal.UnitaryLattice.{u, uV} (padicField v))
    (ω : (padicField v).Carrierˣ →* ℂˣ)
    (hy : PadicSupercuspidal.IsUnitaryCentralCharacter (padicField v) y ω) :
    ∃ ω' : K.Carrierˣ →* ℂˣ,
      PadicSupercuspidal.IsUnitaryCentralCharacter K
          (completionSupercuspidalLatticeEquiv v h K f y) ω' ∧
        ∀ a : K.Carrierˣ, (ω' a : ℂ) = ω (Units.map (f : K.Carrier →* (padicField v).Carrier) a) := by
  subst h
  exact ⟨ω.comp (PadicSupercuspidal.unitsAlgEquiv K (padicFieldAt v rfl) f),
    PadicSupercuspidal.isUnitaryCentralCharacter_unitaryLatticeEquiv K (padicFieldAt v rfl) f
      y ω hy, fun _ => rfl⟩

end Transport

end Langlands.Global

namespace Langlands.Global.PoleComparison

open NumberField Langlands.Weil.Local
open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)
  {p : ℕ} [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
  (f : letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier)

/-- Transport of the determinant clause: if `det x = ω_(T x) ∘ rec_(F_v)` for
every geometric reciprocity candidate of `F_v`, then the composite at `K` has the
determinant clause for every geometric reciprocity candidate of `K`. -/
theorem determinantCompatibility_henniartCompositeMap
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v)
    (hT : ∀ e : Correspondence.ReciprocityCandidate (padicField v),
      Correspondence.IsGeometricReciprocity (padicField v) e →
        RelativeIsometryDeterminantCompatibility F E c v T e)
    (e : Correspondence.ReciprocityCandidate K)
    (he : Correspondence.IsGeometricReciprocity K e) :
    Correspondence.LatticeMap.DeterminantCompatibility K
      (henniartCompositeMap F E c v h K f T) e := by
  obtain ⟨e', he', hrec⟩ := exists_geometric_completionReciprocity v h K f e he
  rintro ⟨x, hx⟩
  obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨ω, hω, hdet⟩ := hT e' he' ⟨x₀, hx₀⟩
  obtain ⟨ω', hω', hω'f⟩ :=
    isUnitaryCentralCharacter_completionSupercuspidalLatticeEquiv v h K f _ ω hω
  have hΦ : (henniartCompositeMap F E c v h K f T ⟨_, hx⟩ :
      PadicSupercuspidal.UnitaryLattice K) =
        completionSupercuspidalLatticeEquiv v h K f (T ⟨x₀, hx₀⟩) :=
    henniartCompositeMap_apply F E c v h K f T ⟨x₀, hx₀⟩
  refine ⟨ω', hΦ ▸ hω', fun w => ?_⟩
  have hw := hdet (completionWeilEquiv v h K f w)
  change ω' (Correspondence.reciprocityHom K e w) = Additive.toMul (LocalWeil.unitaryDeterminant K
    (Weil.restrictUnitaryLatticeEquiv (completionWeilEquiv v h K f) x₀)) w
  have hd := LocalWeil.unitaryDeterminant_restrictUnitaryLatticeEquiv (padicField v) K
    (completionWeilEquiv v h K f) x₀ w
  refine Eq.trans ?_ (hw.trans hd.symm)
  apply Units.ext
  rw [hω'f]
  congr 2
  apply Units.ext
  exact (hrec w).symm

end Langlands.Global.PoleComparison
