import Langlands.AlgebraicGeometry.HenselianFinitePartStatement
import Langlands.AlgebraicGeometry.Morphisms.GenericFiniteness
import Langlands.CommutativeAlgebra.HenselianFiniteNeighborhood

/-! # Finite clopen parts over a Henselian local ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.HenselianFinitePart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_finite_affine_neighborhood
    {R : Type u} [CommRing R] [HenselianLocalRing R] {A : CommRingCat.{u}}
    (φ : CommRingCat.of R ⟶ A)
    [LocallyOfFiniteType (Spec.map φ)] [LocallyQuasiFinite (Spec.map φ)]
    (x : Spec A) (hx : (Spec.map φ) x = IsLocalRing.closedPoint R) :
    ∃ V : (Spec A).Opens, x ∈ V ∧ IsFinite (V.ι ≫ Spec.map φ) := by
  have hft : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp ‹LocallyOfFiniteType _›
  have hqf : φ.hom.QuasiFinite := HasRingHomProperty.Spec_iff.mp ‹LocallyQuasiFinite _›
  algebraize [φ.hom]
  have : x.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨(congrArg PrimeSpectrum.asIdeal hx).symm⟩
  obtain ⟨e, -, he, hfin⟩ :=
    Langlands.CommutativeAlgebra.HenselianFiniteNeighborhood.exists_idempotent_finite_away
      (R := R) x.asIdeal
  refine ⟨PrimeSpectrum.basicOpen e, he, ?_⟩
  have : Module.Finite R (Localization.Away e) := hfin
  have hcomp : φ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away e)) =
      CommRingCat.ofHom (algebraMap R (Localization.Away e)) := by
    ext a
    exact (IsScalarTower.algebraMap_apply R A (Localization.Away e) a).symm
  have : IsFinite
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away e))) ≫ Spec.map φ) := by
    rw [← Spec.map_comp, hcomp]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  rw [← basicOpenIsoSpecAway_hom_SpecMap e, Category.assoc]
  infer_instance

theorem exists_finite_clopen_neighborhood
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsSeparated f]
    (x : X) (hx : f x = IsLocalRing.closedPoint R) :
    ∃ U : X.Opens, x ∈ U ∧ IsClosed (U : Set X) ∧ IsFinite (U.ι ≫ f) := by
  let i := X.affineCover.idx x
  obtain ⟨y, hy⟩ := X.affineCover.covers x
  let c : Spec (Γ(X.affineCover.X i, ⊤)) ⟶ X :=
    (X.affineCover.X i).isoSpec.inv ≫ X.affineCover.f i
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (c ≫ f)
  have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
  have : LocallyQuasiFinite (Spec.map φ) := by rw [hφ]; infer_instance
  let z := (X.affineCover.X i).isoSpec.hom y
  have hz : c z = x := by
    change ((X.affineCover.X i).isoSpec.inv ≫ X.affineCover.f i)
      ((X.affineCover.X i).isoSpec.hom y) = x
    simpa [← Scheme.Hom.comp_apply] using hy
  obtain ⟨V, hzV, hfin⟩ := exists_finite_affine_neighborhood φ z
    (by rw [hφ, Scheme.Hom.comp_apply, hz, hx])
  let j : V.toScheme ⟶ X := V.ι ≫ c
  have : IsOpenImmersion j := inferInstance
  have : IsFinite (j ≫ f) := by
    dsimp [j]
    rw [Category.assoc, ← hφ]
    exact hfin
  have : IsProper j := IsProper.of_comp j f
  refine ⟨j.opensRange, ?_, j.isClosedMap.isClosed_range, ?_⟩
  · exact ⟨⟨z, hzV⟩, hz⟩
  · rw [← Scheme.Hom.isoOpensRange_inv_comp j, Category.assoc]
    infer_instance

/-- An actual finite clopen part containing the whole closed fibre. -/
def finitePart
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [IsSeparated f] :
    {U : X.Opens // IsFiniteClosedFibrePart f U} := by
  classical
  let s : Set X := f ⁻¹' {IsLocalRing.closedPoint R}
  have hs : s.Finite := f.finite_preimage_singleton _
  letI : Fintype s := hs.fintype
  choose U hmem hclosed hfinite using
    fun x : s => exists_finite_clopen_neighborhood f x.1 x.2
  let W : X.Opens := ⨆ x : s, U x
  have hW : IsClosed (W : Set X) := by
    simpa only [W, TopologicalSpace.Opens.coe_iSup] using
      isClosed_iUnion_of_finite hclosed
  have : IsFinite W.ι := GenericFiniteness.isFinite_ι_of_isClosed W hW
  let V : s → W.toScheme.Opens := fun x => W.ι ⁻¹ᵁ U x
  have hcover : ⨆ x : s, V x = ⊤ := by
    apply top_le_iff.mp
    intro w _
    obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp w.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx⟩
  have hVclosed : ∀ x, IsClosed (V x : Set W.toScheme) :=
    fun x => (hclosed x).preimage W.ι.continuous
  have hVfinite : ∀ x, IsFinite ((V x).ι ≫ W.ι ≫ f) := by
    intro x
    dsimp [V]
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    have := hfinite x
    infer_instance
  let e := (Fintype.equivFin s).symm
  have hWfinite : IsFinite (W.ι ≫ f) := by
    apply GenericFiniteness.IsFinite.of_forall_isClosed_of_iSup_eq_top
      (W.ι ≫ f) (V ∘ e)
    · rw [← hcover]
      exact Function.Surjective.iSup_comp e.surjective V
    · exact fun i => hVclosed (e i)
    · exact fun i => hVfinite (e i)
  refine ⟨W, hW, hWfinite, ?_⟩
  intro x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩

end Langlands.AlgebraicGeometry.HenselianFinitePart
