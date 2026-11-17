import Langlands.GroupScheme.Torus.DiagonalizableSourceBaseChange
import Langlands.GroupScheme.Torus.CompleteLocalDeformation.OpenClosed
import Langlands.GroupScheme.Torus.CompleteLocalSimultaneousSplitting
import Langlands.GroupScheme.RelativeLevi.MultiplicationDescent
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # Special-fibre isomorphisms from diagonalizable sources are clopen immersions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The actual pullback-composition comparison preserves and reflects
isomorphisms of base-changed morphisms. -/
theorem isIso_baseChange_comp_iff {S S' S'' : Scheme.{u}}
    (a : S' ⟶ S) (b : S'' ⟶ S') {H G : GroupScheme S} (f : H ⟶ G) :
    IsIso ((GroupScheme.baseChange (b ≫ a)).map f) ↔
      IsIso ((GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map f)) :=
  NatIso.isIso_map_iff
    ((Functor.mapGrpNatIso (Over.pullbackComp b a)) ≪≫ Functor.mapGrpCompIso) f

/-- Isomorphism on special fibres is preserved by a local algebra base change. -/
theorem specialFibre_baseChange_isIso {A B : Type u}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    {H G : GroupScheme (Spec (CommRingCat.of A))} (f : H ⟶ G)
    [IsIso ((GroupScheme.baseChange
      (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f)] :
    IsIso ((GroupScheme.baseChange
      (Spec.algebraMap B (IsLocalRing.ResidueField B))).map
      ((GroupScheme.baseChange (Spec.algebraMap A B)).map f)) := by
  have hc : Spec.algebraMap B (IsLocalRing.ResidueField B) ≫ Spec.algebraMap A B =
      Spec.algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) ≫
        Spec.algebraMap A (IsLocalRing.ResidueField A) := by
    simp only [Spec.algebraMap, ← Spec.map_comp]
    congr 1
  have hs : IsIso ((GroupScheme.baseChange
      (Spec.algebraMap B (IsLocalRing.ResidueField B) ≫ Spec.algebraMap A B)).map f) := by
    rw [hc]
    exact (isIso_baseChange_comp_iff _ _ f).mpr inferInstance
  exact (isIso_baseChange_comp_iff _ _ f).mp hs

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

/-- An explicit idempotent certificate for a coordinate surjection. -/
structure SpecialIsoCoordinateCertificate
    (f : (Diagonalizable.groupScheme (CommRingCat.of R) M).toGrp ⟶ G) where
  surjective : Function.Surjective (diagonalSourceCoordinateMap f).hom
  idempotent : AffineCoordinates.hopfAlgebra G
  isIdempotent : IsIdempotentElem idempotent
  kernel_eq : RingHom.ker (diagonalSourceCoordinateMap f).hom.toAlgHom.toRingHom =
    Ideal.span {idempotent}

/-- A special-fibre isomorphism supplies the actual idempotent-kernel
certificate over a noetherian local base. -/
def specialIsoCoordinateCertificate
    (f : (Diagonalizable.groupScheme (CommRingCat.of R) M).toGrp ⟶ G)
    [IsIso ((GroupScheme.baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f)] :
    SpecialIsoCoordinateCertificate f := by
  classical
  let : IsNoetherianRing (AffineCoordinates.hopfAlgebra G) :=
    coordinate_isNoetherianRing (G := G)
  have : IsIso ((GroupScheme.baseChange
      (Spec.algebraMap R (R ⧸ IsLocalRing.maximalIdeal R))).map f) := by
    change IsIso ((GroupScheme.baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f)
    infer_instance
  let π := (diagonalSourceCoordinateMap f).hom
  have hI : IsLocalRing.maximalIdeal R ≤ Ideal.jacobson (⊥ : Ideal R) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hc := surjective_and_ker_eq_span_idempotent π (IsLocalRing.maximalIdeal R) hI
    (diagonalSourceCoordinates_unit_coeff_of_special_isIso f)
    (diagonalSourceCoordinates_mem_smul_of_baseChange_isIso
      (IsLocalRing.maximalIdeal R) f)
  exact {
    surjective := hc.1
    idempotent := hc.2.choose
    isIdempotent := hc.2.choose_spec.1
    kernel_eq := hc.2.choose_spec.2 }

/-- Over a noetherian local ring, a homomorphism from a diagonalizable group
to an affine finite-type group that is an isomorphism on the special fibre is
an open and closed immersion. -/
theorem open_and_closed_of_special_isIso_diagonalSource
    (f : (Diagonalizable.groupScheme (CommRingCat.of R) M).toGrp ⟶ G)
    [IsIso ((GroupScheme.baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f)] :
    IsOpenImmersion f.hom.hom.left ∧ IsClosedImmersion f.hom.hom.left :=
  open_and_closed_of_diagonalSourceCoordinates f
    (specialIsoCoordinateCertificate f).surjective
    ⟨(specialIsoCoordinateCertificate f).idempotent,
      (specialIsoCoordinateCertificate f).isIdempotent,
      (specialIsoCoordinateCertificate f).kernel_eq⟩

/-- The special-fibre immersion criterion is independent of a choice of
diagonalizable presentation of the source. -/
theorem open_and_closed_of_special_isIso_of_isDiagonalizable
    {H : GroupScheme (Spec (CommRingCat.of R))}
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (f : H ⟶ G)
    [IsIso ((GroupScheme.baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f)] :
    IsOpenImmersion f.hom.hom.left ∧ IsClosedImmersion f.hom.hom.left := by
  obtain ⟨N, _, _, ⟨e⟩⟩ := hH
  let e' := e ≪≫ (Diagonalizable.relativeModelIso (CommRingCat.of R) N).symm
  let f' := e'.inv ≫ f
  have : IsIso ((GroupScheme.baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f') := by
    dsimp only [f']
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨hop, hcl⟩ := open_and_closed_of_special_isIso_diagonalSource f'
  have hf : f = e'.hom ≫ f' := by simp [f']
  rw [hf]
  change IsOpenImmersion (e'.hom.hom.hom.left ≫ f'.hom.hom.left) ∧
    IsClosedImmersion (e'.hom.hom.hom.left ≫ f'.hom.hom.left)
  constructor <;> infer_instance

/-- The immersion half of the complete-local deformation theorem: a
special-fibre isomorphism from a finite-étale-split source is an open and
closed immersion. -/
theorem open_and_closed_of_special_isIso_of_finiteEtaleSplit
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {H : GroupScheme (Spec (CommRingCat.of R))}
    (hH : ∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of R)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange p).obj H))
    (f : H ⟶ G)
    [IsIso ((GroupScheme.baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f)] :
    IsOpenImmersion f.hom.hom.left ∧ IsClosedImmersion f.hom.hom.left := by
  let : HenselianLocalRing R := henselianLocalRing_of_complete R
  let d := localSplitting R H hH
  let B := d.Carrier
  let c := Spec.algebraMap R B
  let : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  have : IsAffine ((GroupScheme.baseChange c).obj G).X.left := by
    change IsAffine (pullback G.X.hom c)
    infer_instance
  have : LocallyOfFiniteType ((GroupScheme.baseChange c).obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd _ _)
    infer_instance
  have : IsIso ((GroupScheme.baseChange
      (Spec.algebraMap B (IsLocalRing.ResidueField B))).map
      ((GroupScheme.baseChange c).map f)) :=
    specialFibre_baseChange_isIso f
  obtain ⟨hop, hcl⟩ := open_and_closed_of_special_isIso_of_isDiagonalizable
    d.split ((GroupScheme.baseChange c).map f)
  have hp : (@Etale ⊓ @Surjective) (pullback.fst G.X.hom c) :=
    ⟨inferInstance, inferInstance⟩
  have hs := RelativeLevi.isPullback_over_baseChange c f.hom.hom
  exact ⟨MorphismProperty.of_isPullback_of_descendsAlong
      (P := @IsOpenImmersion) (Q := @Etale ⊓ @Surjective) hs hp hop,
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @IsClosedImmersion) (Q := @Etale ⊓ @Surjective) hs hp hcl⟩

end Langlands.GroupScheme.CompleteLocalDeformation
