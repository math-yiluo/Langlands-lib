import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableHom
import Langlands.GroupScheme.Torus.CentralExtensionHopfSpec
import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli

/-! # Split-torus homomorphisms as Hopf points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme

section ClosedImmersion

variable {S : Scheme.{u}} {H G H' G' : GroupScheme S}

/-- Transport along isomorphisms of source and target preserves and reflects closed
immersions. -/
theorem isClosedSubgroup_transport_iff (eH : H' ≅ H) (eG : G ≅ G') {T : Over S}
    (i : RelativeHom H G T) :
    IsClosedSubgroup (transport eH eG i) ↔ IsClosedSubgroup i := by
  let he : IsIso ((baseChange T.hom).map eH.hom).hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso ((baseChange T.hom).map eH.hom)
  let hg : IsIso ((baseChange T.hom).map eG.hom).hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso ((baseChange T.hom).map eG.hom)
  change IsClosedImmersion (((baseChange T.hom).map eH.hom).hom.hom.left ≫ i.hom.hom.left ≫
    ((baseChange T.hom).map eG.hom).hom.hom.left) ↔ IsClosedImmersion i.hom.hom.left
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]

end ClosedImmersion

section Range

/-- The range of one homomorphism lies in the range of another exactly when the first factors
through the second on underlying schemes. -/
theorem range_le_range_iff {B : Scheme.{u}} {K K' G : GroupScheme B} (j : K ⟶ G)
    (j' : K' ⟶ G) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range j' ↔
      ∃ z : K.X.left ⟶ K'.X.left, z ≫ j'.hom.hom.left = j.hom.hom.left := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := SubgroupFunctor.le_def.mp h K.X
      (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩)
    exact ⟨y.left, by rw [← hy]; rfl⟩
  · rintro ⟨z, hz⟩
    rw [SubgroupFunctor.le_def]
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    let z' : K.X ⟶ K'.X := Over.homMk z (by
      rw [← Over.w j.hom.hom, ← hz, Category.assoc, Over.w j'.hom.hom])
    refine SubgroupFunctor.mem_range.mpr ⟨y ≫ z', ?_⟩
    apply Over.OverMorphism.ext
    simp only [z', Over.comp_left, Over.homMk_left, Category.assoc, hz]

variable {S : Scheme.{u}} {H G H' G' : GroupScheme S}

/-- Transport along isomorphisms of source and target preserves and reflects inclusions of
ranges. -/
theorem range_transport_le_iff (eH : H' ≅ H) (eG : G ≅ G') {T : Over S}
    (i i' : RelativeHom H G T) :
    SubgroupFunctor.range (transport eH eG i') ≤ SubgroupFunctor.range (transport eH eG i) ↔
      SubgroupFunctor.range i' ≤ SubgroupFunctor.range i := by
  rw [range_le_range_iff, range_le_range_iff]
  let a := ((baseChange T.hom).map eH.hom).hom.hom.left
  let b := ((baseChange T.hom).map eG.hom).hom.hom.left
  have ha : IsIso a := (Grp.forget _ ⋙ Over.forget _).map_isIso ((baseChange T.hom).map eH.hom)
  have hb : IsIso b := (Grp.forget _ ⋙ Over.forget _).map_isIso ((baseChange T.hom).map eG.hom)
  change (∃ z, z ≫ a ≫ i.hom.hom.left ≫ b = a ≫ i'.hom.hom.left ≫ b) ↔
    ∃ z, z ≫ i.hom.hom.left = i'.hom.hom.left
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨inv a ≫ z ≫ a, ?_⟩
    rw [← cancel_mono b, ← cancel_epi a]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hz
  · rintro ⟨z, hz⟩
    exact ⟨a ≫ z ≫ inv a, by simp only [Category.assoc, IsIso.inv_hom_id_assoc, reassoc_of% hz]⟩

/-- The evaluated subgroup family of a relative homomorphism is the evaluated relative
homomorphism, up to the source pullback comparison. -/
theorem familyHom_eq {T T' : Over S} (i : RelativeHom H G T) (a : T' ⟶ T) :
    TorusSubgroupModuli.familyHom i a =
      (Descent.pullbackComparison T.hom a.left T'.hom (Over.w a) H).hom ≫ evaluate a i := by
  rw [evaluate, Descent.pullHom, Iso.hom_inv_id_assoc]
  rfl

/-- Range compatibility: evaluating a relative homomorphism as a subgroup family gives the
range of the evaluated homomorphism. -/
theorem evaluate_eq_range {T T' : Over S} (i : RelativeHom H G T) (a : T' ⟶ T) :
    TorusSubgroupModuli.evaluate i a = SubgroupFunctor.range (evaluate a i) := by
  rw [TorusSubgroupModuli.evaluate, familyHom_eq, SubgroupFunctor.range_iso_comp]

end Range

namespace FiniteSource

open Langlands.FiniteBialgebraHom

variable {R : Type u} [CommRing R] {A P : Type u} [CommRing A] [CommRing P] [HopfAlgebra R A]
  [HopfAlgebra R P]

/-- The homomorphism attached to a Hopf point is a closed immersion exactly when the
`C`-linear extension `C ⊗[R] A → C ⊗[R] P` of the point is surjective. -/
theorem isClosedSubgroup_pointEquiv_symm_iff {C : Type u} [CommRing C] [Algebra R C]
    (f : {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f}) :
    IsClosedSubgroup ((pointEquiv A P C).symm f) ↔
      Function.Surjective (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1) := by
  let φ : CommRingCat.of (C ⊗[R] A) ⟶ CommRingCat.of (C ⊗[R] P) :=
    CommRingCat.ofHom (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1).toRingHom
  have h : ((pointEquiv A P C).symm f).hom.hom.left =
      (tensorIso P C).hom ≫ Spec.map φ ≫ (tensorIso A C).inv :=
    rfl
  change IsClosedImmersion ((pointEquiv A P C).symm f).hom.hom.left ↔ Function.Surjective φ
  rw [h, MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]
  constructor
  · intro hc
    exact CentralExtensionHopfSpec.surjective_of_isClosedImmersion φ
  · exact IsClosedImmersion.spec_of_surjective φ

/-- Inclusion of ranges of homomorphisms attached to Hopf points: the range of `f'` lies in the
range of `f` exactly when the `C`-linear extension of `f'` factors through that of `f` by a ring
endomorphism of `C ⊗[R] P`. -/
theorem range_pointEquiv_symm_le_iff {C : Type u} [CommRing C] [Algebra R C]
    (f f' : {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f}) :
    SubgroupFunctor.range ((pointEquiv A P C).symm f') ≤
        SubgroupFunctor.range ((pointEquiv A P C).symm f) ↔
      ∃ ψ : C ⊗[R] P →+* C ⊗[R] P,
        ψ.comp (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1).toRingHom =
          (AlgHom.liftEquiv R C A (C ⊗[R] P) f'.1).toRingHom := by
  let φ : CommRingCat.of (C ⊗[R] A) ⟶ CommRingCat.of (C ⊗[R] P) :=
    CommRingCat.ofHom (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1).toRingHom
  let φ' : CommRingCat.of (C ⊗[R] A) ⟶ CommRingCat.of (C ⊗[R] P) :=
    CommRingCat.ofHom (AlgHom.liftEquiv R C A (C ⊗[R] P) f'.1).toRingHom
  have h : ((pointEquiv A P C).symm f).hom.hom.left =
      (tensorIso P C).hom ≫ Spec.map φ ≫ (tensorIso A C).inv :=
    rfl
  have h' : ((pointEquiv A P C).symm f').hom.hom.left =
      (tensorIso P C).hom ≫ Spec.map φ' ≫ (tensorIso A C).inv :=
    rfl
  rw [range_le_range_iff, h, h']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(Spec.preimage ((tensorIso P C).inv ≫ z ≫ (tensorIso P C).hom)).hom, ?_⟩
    have hmap : Spec.map (φ ≫ Spec.preimage ((tensorIso P C).inv ≫ z ≫ (tensorIso P C).hom)) =
        Spec.map φ' := by
      rw [Spec.map_comp, Spec.map_preimage, ← cancel_epi (tensorIso P C).hom,
        ← cancel_mono (tensorIso A C).inv]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hz
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hmap)
  · rintro ⟨ψ, hψ⟩
    refine ⟨(tensorIso P C).hom ≫ Spec.map (CommRingCat.ofHom ψ) ≫ (tensorIso P C).inv, ?_⟩
    have hcomp : φ ≫ CommRingCat.ofHom ψ = φ' := CommRingCat.hom_ext hψ
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc, hcomp]

/-- Kernel form of `range_pointEquiv_symm_le_iff` when the `C`-linear extension of `f` is
surjective (that is, when the homomorphism attached to `f` is a closed immersion). -/
theorem range_pointEquiv_symm_le_iff_ker {C : Type u} [CommRing C] [Algebra R C]
    (f f' : {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1)) :
    SubgroupFunctor.range ((pointEquiv A P C).symm f') ≤
        SubgroupFunctor.range ((pointEquiv A P C).symm f) ↔
      RingHom.ker (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1) ≤
        RingHom.ker (AlgHom.liftEquiv R C A (C ⊗[R] P) f'.1) := by
  rw [range_pointEquiv_symm_le_iff]
  constructor
  · rintro ⟨ψ, hψ⟩ x hx
    rw [RingHom.mem_ker] at hx ⊢
    have hx' := congrArg (· x) hψ
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] at hx'
    rw [← hx', hx, map_zero]
  · intro hker
    let φ := (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1).toRingHom
    let φ' := (AlgHom.liftEquiv R C A (C ⊗[R] P) f'.1).toRingHom
    have hφ : Function.Surjective φ := hf
    refine ⟨(Ideal.Quotient.lift (RingHom.ker φ) φ' (fun x hx => hker hx)).comp
      (RingHom.quotientKerEquivOfSurjective hφ).symm.toRingHom, ?_⟩
    apply RingHom.ext
    intro x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]

/-- Two closed immersions attached to Hopf points have the same range exactly when the kernels
of their `C`-linear extensions agree. -/
theorem range_pointEquiv_symm_eq_iff_ker {C : Type u} [CommRing C] [Algebra R C]
    (f f' : {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1))
    (hf' : Function.Surjective (AlgHom.liftEquiv R C A (C ⊗[R] P) f'.1)) :
    SubgroupFunctor.range ((pointEquiv A P C).symm f) =
        SubgroupFunctor.range ((pointEquiv A P C).symm f') ↔
      RingHom.ker (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1) =
        RingHom.ker (AlgHom.liftEquiv R C A (C ⊗[R] P) f'.1) := by
  rw [le_antisymm_iff, le_antisymm_iff, range_pointEquiv_symm_le_iff_ker f' f hf',
    range_pointEquiv_symm_le_iff_ker f f' hf]
  exact and_comm

/-- Composing a Hopf point with a `C`-algebra endomorphism of `C ⊗[R] P` shrinks the range. -/
theorem range_pointEquiv_symm_le_of_comp {C : Type u} [CommRing C] [Algebra R C]
    (τ : C ⊗[R] P →ₐ[C] C ⊗[R] P) (f f' : {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f})
    (h : f'.1 = (τ.restrictScalars R).comp f.1) :
    SubgroupFunctor.range ((pointEquiv A P C).symm f') ≤
      SubgroupFunctor.range ((pointEquiv A P C).symm f) := by
  rw [range_pointEquiv_symm_le_iff]
  refine ⟨τ.toRingHom, ?_⟩
  have hlift : AlgHom.liftEquiv R C A (C ⊗[R] P) f'.1 =
      τ.comp (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1) := by
    apply (AlgHom.liftEquiv R C A (C ⊗[R] P)).symm.injective
    rw [Equiv.symm_apply_apply, h]
    ext a
    simp
  rw [hlift]
  rfl

end FiniteSource

namespace SplitTorusPoint

open Langlands.FiniteBialgebraHom FiniteSource FiniteDiagonalizable

variable (R : Type u) [CommRing R] (I : Type u) [Fintype I] [DecidableEq I]

/-- The Hopf spectrum of the group algebra `R[ℤ^I]` is the split torus `𝔾_m^I`. -/
def splitTorusHopfIso :
    hopfGroup R (AddMonoidAlgebra R (I → ℤ)) ≅ splitTorus (Spec (CommRingCat.of R)) I :=
  Diagonalizable.hopfSpecIso (CommRingCat.of R) (I → ℤ) ≪≫
    Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (I → ℤ))

variable {R I} (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]

/-- Homomorphisms from the split torus `𝔾_m^I` to `G` after base change to `Spec C` are
Hopf points `O(G) → C ⊗[R] R[ℤ^I]`. -/
def splitPointEquiv (C : Type u) [CommRing C] [Algebra R C] :
    RelativeHom (splitTorus (Spec (CommRingCat.of R)) I) G (specOver R C) ≃
      {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
        IsHopfPoint R f} :=
  (transportEquiv (splitTorusHopfIso R I).symm (coordinateIso G) (specOver R C)).symm.trans
    (pointEquiv _ _ C)

variable {G}

theorem splitPointEquiv_symm_apply {C : Type u} [CommRing C] [Algebra R C]
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      IsHopfPoint R f}) :
    (splitPointEquiv G C).symm f =
      transport (splitTorusHopfIso R I).symm (coordinateIso G) ((pointEquiv _ _ C).symm f) :=
  rfl

/-- Naturality: evaluation along `Spec D ⟶ Spec C` pushes the Hopf point forward along
`C → D`. -/
theorem evaluate_splitPointEquiv_symm {C D : Type u} [CommRing C] [Algebra R C] [CommRing D]
    [Algebra R D] (g : C →ₐ[R] D)
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      IsHopfPoint R f}) :
    evaluate (specMap g) ((splitPointEquiv G C).symm f) =
      (splitPointEquiv G D).symm ⟨pushPoint R g f.1, f.2.pushPoint R g⟩ := by
  rw [splitPointEquiv_symm_apply, evaluate_transport, evaluate_specMap]
  rfl

/-- Naturality, read on Hopf points. -/
theorem splitPointEquiv_evaluate {C D : Type u} [CommRing C] [Algebra R C] [CommRing D]
    [Algebra R D] (g : C →ₐ[R] D)
    (j : RelativeHom (splitTorus (Spec (CommRingCat.of R)) I) G (specOver R C)) :
    (splitPointEquiv G D (evaluate (specMap g) j)).1 =
      pushPoint R g (splitPointEquiv G C j).1 := by
  obtain ⟨f, rfl⟩ := (splitPointEquiv G C).symm.surjective j
  rw [evaluate_splitPointEquiv_symm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The split-torus homomorphism attached to a Hopf point is a closed immersion exactly when
the `C`-linear extension `C ⊗[R] O(G) → C ⊗[R] R[ℤ^I]` of the point is surjective. -/
theorem isClosedSubgroup_splitPointEquiv_symm_iff {C : Type u} [CommRing C] [Algebra R C]
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      IsHopfPoint R f}) :
    IsClosedSubgroup ((splitPointEquiv G C).symm f) ↔
      Function.Surjective (AlgHom.liftEquiv R C _ _ f.1) := by
  rw [splitPointEquiv_symm_apply, isClosedSubgroup_transport_iff,
    isClosedSubgroup_pointEquiv_symm_iff]

/-- Range compatibility for split-torus homomorphisms: evaluating along `Spec D ⟶ Spec C`
gives the range of the homomorphism of the pushed-forward Hopf point. -/
theorem evaluate_splitPointEquiv_symm_eq_range {C D : Type u} [CommRing C] [Algebra R C]
    [CommRing D] [Algebra R D] (g : C →ₐ[R] D)
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      IsHopfPoint R f}) :
    TorusSubgroupModuli.evaluate ((splitPointEquiv G C).symm f) (specMap g) =
      SubgroupFunctor.range ((splitPointEquiv G D).symm ⟨pushPoint R g f.1, f.2.pushPoint R g⟩) := by
  rw [evaluate_eq_range, evaluate_splitPointEquiv_symm]

/-- Inclusion of ranges of split-torus homomorphisms, read on Hopf points. -/
theorem range_splitPointEquiv_symm_le_iff {C : Type u} [CommRing C] [Algebra R C]
    (f f' : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      IsHopfPoint R f}) :
    SubgroupFunctor.range ((splitPointEquiv G C).symm f') ≤
        SubgroupFunctor.range ((splitPointEquiv G C).symm f) ↔
      ∃ ψ : C ⊗[R] AddMonoidAlgebra R (I → ℤ) →+* C ⊗[R] AddMonoidAlgebra R (I → ℤ),
        ψ.comp (AlgHom.liftEquiv R C _ _ f.1).toRingHom =
          (AlgHom.liftEquiv R C _ _ f'.1).toRingHom := by
  rw [splitPointEquiv_symm_apply, splitPointEquiv_symm_apply, range_transport_le_iff,
    range_pointEquiv_symm_le_iff]

/-- Kernel form of `range_splitPointEquiv_symm_le_iff` when the homomorphism attached to `f`
is a closed immersion. -/
theorem range_splitPointEquiv_symm_le_iff_ker {C : Type u} [CommRing C] [Algebra R C]
    (f f' : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R C _ _ f.1)) :
    SubgroupFunctor.range ((splitPointEquiv G C).symm f') ≤
        SubgroupFunctor.range ((splitPointEquiv G C).symm f) ↔
      RingHom.ker (AlgHom.liftEquiv R C _ _ f.1) ≤ RingHom.ker (AlgHom.liftEquiv R C _ _ f'.1) := by
  rw [splitPointEquiv_symm_apply, splitPointEquiv_symm_apply, range_transport_le_iff,
    range_pointEquiv_symm_le_iff_ker f f' hf]

/-- Two closed split-torus homomorphisms have the same range exactly when the kernels of the
`C`-linear extensions of their Hopf points agree. -/
theorem range_splitPointEquiv_symm_eq_iff_ker {C : Type u} [CommRing C] [Algebra R C]
    (f f' : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R C _ _ f.1))
    (hf' : Function.Surjective (AlgHom.liftEquiv R C _ _ f'.1)) :
    SubgroupFunctor.range ((splitPointEquiv G C).symm f) =
        SubgroupFunctor.range ((splitPointEquiv G C).symm f') ↔
      RingHom.ker (AlgHom.liftEquiv R C _ _ f.1) = RingHom.ker (AlgHom.liftEquiv R C _ _ f'.1) := by
  rw [le_antisymm_iff, le_antisymm_iff, range_splitPointEquiv_symm_le_iff_ker f' f hf',
    range_splitPointEquiv_symm_le_iff_ker f f' hf]
  exact and_comm

/-- Twisting a Hopf point by an endomorphism `t` of the character lattice `ℤ^I` shrinks the
range of the attached homomorphism. -/
theorem range_splitPointEquiv_symm_twist_le {C : Type u} [CommRing C] [Algebra R C]
    (t : (I → ℤ) →+ (I → ℤ))
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      IsHopfPoint R f})
    (h : IsHopfPoint R ((Algebra.TensorProduct.map (AlgHom.id R C)
      (AddMonoidAlgebra.mapDomainAlgHom R R t)).comp f.1)) :
    SubgroupFunctor.range ((splitPointEquiv G C).symm ⟨_, h⟩) ≤
      SubgroupFunctor.range ((splitPointEquiv G C).symm f) := by
  rw [splitPointEquiv_symm_apply, splitPointEquiv_symm_apply, range_transport_le_iff]
  refine range_pointEquiv_symm_le_of_comp
    (Algebra.TensorProduct.map (AlgHom.id C C) (AddMonoidAlgebra.mapDomainAlgHom R R t)) f _ ?_
  congr 1

/-- Twisting a Hopf point by an automorphism `t` of the character lattice `ℤ^I` does not change
the range of the attached homomorphism. -/
theorem range_splitPointEquiv_symm_twist_eq {C : Type u} [CommRing C] [Algebra R C]
    (t : (I → ℤ) ≃+ (I → ℤ))
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      IsHopfPoint R f})
    (h : IsHopfPoint R ((Algebra.TensorProduct.map (AlgHom.id R C)
      (AddMonoidAlgebra.mapDomainAlgHom R R t.toAddMonoidHom)).comp f.1)) :
    SubgroupFunctor.range ((splitPointEquiv G C).symm ⟨_, h⟩) =
      SubgroupFunctor.range ((splitPointEquiv G C).symm f) := by
  refine le_antisymm (range_splitPointEquiv_symm_twist_le _ f h) ?_
  rw [splitPointEquiv_symm_apply, splitPointEquiv_symm_apply, range_transport_le_iff]
  refine range_pointEquiv_symm_le_of_comp
    (Algebra.TensorProduct.map (AlgHom.id C C)
      (AddMonoidAlgebra.mapDomainAlgHom R R t.symm.toAddMonoidHom)) _ f ?_
  apply AlgHom.ext
  intro a
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply]
  induction f.1 a using TensorProduct.inductionOn with
  | tmul c p =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    congr 1
    rw [← AlgHom.comp_apply, ← AddMonoidAlgebra.mapDomainAlgHom_comp]
    simp
  | add x y hx hy => rw [map_add, map_add, ← hx, ← hy]

end SplitTorusPoint

end Langlands.GroupScheme.HomScheme
