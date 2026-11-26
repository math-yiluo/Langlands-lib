import Langlands.Geometry.Analytic.StrongEtaleSourceOpenLocality
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.LocalizedEtaleComposition

/-! # Source-open locality of localized analytic étaleness -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Set Topology TopologicalSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : LocalizedCategory.{u, v, v} (K := K)}

/-- The locus of points with an open source restriction on which the given analytic
morphism is étale. -/
def localizedSourceOpenEtaleLocus (f : X ⟶ Y) : Set (localizedSpaceFunctor.obj X) :=
  {x | ∃ (U : Set (localizedSpaceFunctor.obj X)) (hU : IsOpen U),
    x ∈ U ∧ etale (domainι X ((presentationOf X).openDomain U hU) ≫ f)}

/-- Étaleness on an open source restriction gives an open subset of the locus. -/
theorem isOpen_localizedSourceOpenEtaleLocus (f : X ⟶ Y) :
    IsOpen (localizedSourceOpenEtaleLocus f) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro x ⟨U, hU, hx, hf⟩
  exact Filter.mem_of_superset (hU.mem_nhds hx) (fun _ hy => ⟨U, hU, hy, hf⟩)

/-- A localized analytic map is étale if its restrictions to an open cover of the source
are étale. Transfer those restrictions along the denominator homeomorphism of a right
fraction and apply strong étale locality to its numerator. -/
theorem etale_of_open_source_cover (f : X ⟶ Y) {I : Type*}
    (U : I → Set (localizedSpaceFunctor.obj X)) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i)
    (hf : ∀ i, etale (domainι X ((presentationOf X).openDomain (U i) (hU i)) ≫ f)) : etale f := by
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
  obtain ⟨B, rfl⟩ := localizedObjectEquiv.surjective Y
  change I → Set A.presentation.space at U
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  rw [← localizedFractionEtale_eq_etale]
  refine (localizedFractionEtale_iff (localizedRightFraction φ)).mpr ⟨φ, rfl, ?_⟩
  let e := localizedQuasiIso φ.s φ.hs
  let e₀ : φ.X'.presentation.space ≃ₜ A.presentation.space :=
    TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)
  let V (i : I) : Set φ.X'.presentation.space := e₀ ⁻¹' U i
  have hV (i : I) : IsOpen (V i) := (hU i).preimage e₀.continuous
  refine strongEtale_of_open_source_cover φ.f V hV (fun x => hcover (e₀ x)) ?_
  intro i
  let D := φ.X'.openDomain (V i) (hV i)
  let E := A.openDomain (U i) (hU i)
  have heD (x : φ.X'.presentation.space) (hx : x ∈ D.carrier) : e₀ x ∈ E.carrier := hx
  have heE (y : A.presentation.space) (hy : y ∈ E.carrier) : e₀.symm y ∈ D.carrier := by
    change e₀ (e₀.symm y) ∈ U i
    exact (e₀.apply_symm_apply y).symm ▸ hy
  let eD := domainRestrictIso e D E heD heE
  rw [← etale_localizationFunctor_map_iff_strongEtale, Functor.map_comp]
  let j := domainι (localizationFunctor.obj φ.X') D
  let k := domainι (localizationFunctor.obj A) E
  change etale (j ≫ localizationFunctor.map φ.f)
  have he : eD.hom ≫ k ≫ localizedRightFraction φ = j ≫ localizationFunctor.map φ.f := by
    calc
      _ = (eD.hom ≫ k) ≫ localizedRightFraction φ := (Category.assoc _ _ _).symm
      _ = (j ≫ e.hom) ≫ localizedRightFraction φ :=
        congrArg (· ≫ localizedRightFraction φ) (domainRestrictIso_hom_inclusion e D E heD heE)
      _ = j ≫ e.hom ≫ e.inv ≫ localizationFunctor.map φ.f := Category.assoc _ _ _
      _ = _ := congrArg (j ≫ ·) (e.hom_inv_id_assoc _)
  exact he ▸ etale_comp (etale_of_isIso eD.hom) (hf i)

/-- The open source locus is the whole source exactly for an étale map. -/
theorem localizedSourceOpenEtaleLocus_eq_univ_iff (f : X ⟶ Y) :
    localizedSourceOpenEtaleLocus f = Set.univ ↔ etale f := by
  constructor
  · intro h
    let I := {U : Opens (localizedSpaceFunctor.obj X) //
      etale (domainι X ((presentationOf X).openDomain U.carrier U.isOpen) ≫ f)}
    refine etale_of_open_source_cover f (fun i : I => i.val) (fun i => i.val.isOpen) ?_
      (fun i => i.property)
    intro x
    have hx : x ∈ localizedSourceOpenEtaleLocus f := h.symm ▸ Set.mem_univ x
    obtain ⟨U, hU, hx, hf⟩ := hx
    exact ⟨⟨⟨U, hU⟩, hf⟩, hx⟩
  · intro hf
    apply Set.eq_univ_of_forall
    intro x
    exact ⟨Set.univ, isOpen_univ, Set.mem_univ x,
      etale_comp (etaleOpenDomainStatement X Set.univ isOpen_univ) hf⟩

end Langlands.Analytic.SaturatedAtlasPresentation
