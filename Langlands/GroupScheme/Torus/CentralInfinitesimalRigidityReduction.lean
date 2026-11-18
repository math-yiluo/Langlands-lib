import Langlands.GroupScheme.LeftRightAction
import Langlands.GroupScheme.HomEqualityOpenLocus
import Langlands.GroupScheme.FppfHomLocality
import Langlands.GroupScheme.Torus.MultiplicativeTypeAffineInfinitesimalCentrality

/-! # Central infinitesimal uniqueness from diagonalizable action rigidity -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.CentralInfinitesimalRigidity

variable {R : CommRingCat.{u}}

/-- An affine test algebra annihilating an ideal is an actual scheme over the quotient base. -/
def quotientTest (I : Ideal R) (C : CommAlgCat.{u} R)
    (hC : ∀ r : R, r ∈ I → algebraMap R C r = 0) :
    Over (Spec (CommRingCat.of (R ⧸ I))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I (algebraMap R C) hC)))

/-- Forgetting the quotient-base structure recovers the original affine test scheme. -/
theorem quotientTest_comp (I : Ideal R) (C : CommAlgCat.{u} R)
    (hC : ∀ r : R, r ∈ I → algebraMap R C r = 0) :
    (quotientTest I C hC).hom ≫ Spec.algebraMap R (R ⧸ I) =
      ((algSpec R).obj (op C)).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

/-- Equality after pullback gives equality on every test whose structure map
factors through that base change. -/
theorem eq_on_test_of_pullback_map_eq {S T : Scheme.{u}} (b : T ⟶ S)
    {X Y : Over S} (f g : X ⟶ Y)
    (he : (Over.pullback b).map f = (Over.pullback b).map g)
    (V : Over S) (c : V.left ⟶ T) (hc : c ≫ b = V.hom) (x : V ⟶ X) :
    x ≫ f = x ≫ g := by
  let x' : Over.mk c ⟶ (Over.pullback b).obj X :=
    Over.homMk (pullback.lift x.left c ((Over.w x).trans hc.symm))
      (pullback.lift_snd _ _ _)
  have h := congrArg (fun a => x'.left ≫ a.left ≫ pullback.fst Y.hom b) he
  apply Over.OverMorphism.ext
  simpa only [x', Over.homMk_left, Over.pullback_map_left, Category.assoc,
    pullback.lift_fst, pullback.lift_fst_assoc, Over.comp_left] using h

/-- Triviality after the quotient base change gives the affine-test hypothesis
used by diagonalizable action rigidity. -/
theorem action_trivial_on_quotient_test
    {H G : GroupScheme (Spec R)} (a : SchemeAction H G.X) (I : Ideal R)
    (he : Functor.LaxMonoidal.μ (Over.pullback (Spec.algebraMap R (R ⧸ I))) H.X G.X ≫
        (Over.pullback (Spec.algebraMap R (R ⧸ I))).map a.hom =
      snd ((baseChange (Spec.algebraMap R (R ⧸ I))).obj H).X
        ((baseChange (Spec.algebraMap R (R ⧸ I))).obj G).X)
    (C : CommAlgCat.{u} R) (hC : ∀ r : R, r ∈ I → algebraMap R C r = 0)
    (t : (algSpec R).obj (op C) ⟶ H.X) (x : (algSpec R).obj (op C) ⟶ G.X) :
    a.act t x = x := by
  let b := Spec.algebraMap R (R ⧸ I)
  have he' : (Over.pullback b).map a.hom = (Over.pullback b).map (snd H.X G.X) := by
    apply (cancel_epi (Functor.LaxMonoidal.μ (Over.pullback b) H.X G.X)).mp
    rw [he, Functor.Monoidal.μ_snd]
    rfl
  have h := eq_on_test_of_pullback_map_eq b a.hom (snd H.X G.X) he'
    ((algSpec R).obj (op C)) (quotientTest I C hC).hom
    (quotientTest_comp I C hC) (lift t x)
  simpa only [SchemeAction.act, lift_snd] using h

/-- The action-rigidity input, for all diagonalizable groups and arbitrary scheme targets. -/
def DiagonalizableActionRigidityInput : Prop :=
  ∀ (R : CommRingCat.{u}) (M : Type u) [AddCommGroup M]
    (X : Over (Spec R)) (a : SchemeAction (Diagonalizable.groupScheme R M).toGrp X)
    (I : Ideal R), IsNilpotent I →
    (∀ C : CommAlgCat.{u} R,
      (∀ r : R, r ∈ I → algebraMap R C r = 0) →
      ∀ (t : (algSpec R).obj (op C) ⟶ (Diagonalizable.groupScheme R M).X)
        (x : (algSpec R).obj (op C) ⟶ X), a.act t x = x) →
    a.hom = snd (Diagonalizable.groupScheme R M).X X

/-- Diagonalizable action rigidity gives uniqueness for two homomorphisms
with the same central nilpotent reduction. -/
theorem diagonalizable_central_uniqueness (hact : DiagonalizableActionRigidityInput.{u})
    (M : Type u) [AddCommGroup M] {G : GroupScheme (Spec R)}
    (f g : (Diagonalizable.groupScheme R M).toGrp ⟶ G)
    (I : Ideal R) (hI : IsNilpotent I)
    (he : (baseChange (Spec.algebraMap R (R ⧸ I))).map f =
      (baseChange (Spec.algebraMap R (R ⧸ I))).map g)
    (hc : IsCentral ((baseChange (Spec.algebraMap R (R ⧸ I))).map f)) : f = g := by
  apply ((leftRightHom_eq_snd_iff f g).mp ?_).1
  change (leftRightAction f g).hom = _
  apply hact R M G.X (leftRightAction f g) I hI
  intro C hC t x
  apply action_trivial_on_quotient_test (leftRightAction f g) I _ C hC t x
  rw [leftRightAction_hom, baseChange_leftRightHom]
  exact (leftRightHom_eq_snd_iff _ _).mpr ⟨he, hc⟩

/-- The same uniqueness assertion for any supplied relative diagonalizable presentation. -/
theorem isDiagonalizable_central_uniqueness (hact : DiagonalizableActionRigidityInput.{u})
    {H G : GroupScheme (Spec R)} (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (f g : H ⟶ G) (I : Ideal R) (hI : IsNilpotent I)
    (he : (baseChange (Spec.algebraMap R (R ⧸ I))).map f =
      (baseChange (Spec.algebraMap R (R ⧸ I))).map g)
    (hc : IsCentral ((baseChange (Spec.algebraMap R (R ⧸ I))).map f)) : f = g := by
  obtain ⟨M, _, _, ⟨e⟩⟩ := hH
  let d : (Diagonalizable.groupScheme R M).toGrp ≅ H :=
    (Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) M).symm ≪≫ e.symm
  apply (cancel_epi d.hom).mp
  apply diagonalizable_central_uniqueness hact M _ _ I hI
  · simp only [Functor.map_comp, he]
  · simpa only [Functor.map_comp] using
      hc.comp ((baseChange (Spec.algebraMap R (R ⧸ I))).map d.hom)

set_option maxHeartbeats 800000 in
/-- Equality after a nilpotent quotient is detected on any affine base chart
where the source becomes diagonalizable. -/
theorem central_uniqueness_on_affine_chart
    (hact : DiagonalizableActionRigidityInput.{u}) {B : CommRingCat.{u}}
    (b : Spec B ⟶ Spec R) {H G : GroupScheme (Spec R)}
    (hdiag : RelativeMultiplicativeType.IsDiagonalizable ((baseChange b).obj H))
    (f g : H ⟶ G) (J : Ideal R) (hJ : IsNilpotent J)
    (he : (baseChange (Spec.algebraMap R (R ⧸ J))).map f =
      (baseChange (Spec.algebraMap R (R ⧸ J))).map g)
    (hc : IsCentral ((baseChange (Spec.algebraMap R (R ⧸ J))).map f)) :
    (baseChange b).map f = (baseChange b).map g := by
  let : Algebra R B := (Spec.preimage b).hom.toAlgebra
  have hb : Spec.algebraMap R B = b := Spec.map_preimage b
  let JB := J.map (algebraMap R B)
  have hJB : IsNilpotent JB :=
    MultiplicativeTypeAffineInfinitesimalCentrality.isNilpotent_map J hJ
  have hcB : IsCentral ((baseChange (Spec.algebraMap B (B ⧸ JB))).map
      ((baseChange b).map f)) := by
    rw [← hb]
    exact MultiplicativeTypeAffineInfinitesimalCentrality.isCentral_quotient_baseChange f J hc
  let q := Spec.algebraMap B (B ⧸ JB)
  let r := Spec.algebraMap R (R ⧸ J)
  let φ : R ⧸ J →+* B ⧸ JB :=
    Ideal.quotientMap JB (algebraMap R B) Ideal.le_comap_map
  have hsquare : q ≫ b = Spec.map (CommRingCat.ofHom φ) ≫ r := by
    rw [← hb]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have heB : (baseChange q).map ((baseChange b).map f) =
      (baseChange q).map ((baseChange b).map g) := by
    apply (HomEqualityOpenLocus.iterated_baseChange_eq_iff b q (q ≫ b) rfl f g).mpr
    exact HomEqualityOpenLocus.baseChange_eq_of_factor r
      (Spec.map (CommRingCat.ofHom φ)) (q ≫ b) hsquare.symm he
  exact isDiagonalizable_central_uniqueness hact hdiag _ _ JB hJB heB hcB

set_option maxHeartbeats 800000 in
/-- Central infinitesimal uniqueness descends through the source's fppf diagonalizing cover. -/
theorem central_uniqueness_over_commRingCat
    (hact : DiagonalizableActionRigidityInput.{u}) (J : Ideal R) (hJ : IsNilpotent J)
    (G H : GroupScheme (Spec R)) (f g : H ⟶ G)
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (he : (baseChange (Spec.algebraMap R (R ⧸ J))).map f =
      (baseChange (Spec.algebraMap R (R ⧸ J))).map g)
    (hc : IsCentral ((baseChange (Spec.algebraMap R (R ⧸ J))).map f)) : f = g := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  apply hom_ext_of_pointwise_fppf_baseChange
  intro s
  obtain ⟨i, t, ht⟩ := 𝒰.exists_eq s
  obtain ⟨j, z, hz⟩ := (𝒰.X i).affineCover.exists_eq t
  let B := (𝒰.X i).affineOpenCover.X j
  let c := (𝒰.X i).affineOpenCover.f j
  let b : Spec B ⟶ Spec R := c ≫ 𝒰.f i
  have : IsOpenImmersion c := (𝒰.X i).affineOpenCover.map_prop j
  have : Flat c := inferInstance
  have : LocallyOfFinitePresentation c := inferInstance
  have : Flat (𝒰.f i) := (𝒰.map_prop i).1
  have : LocallyOfFinitePresentation (𝒰.f i) := (𝒰.map_prop i).2
  have hbflat : Flat b := inferInstance
  have hblfp : LocallyOfFinitePresentation b := inferInstance
  have hdiag : RelativeMultiplicativeType.IsDiagonalizable ((baseChange b).obj H) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (Descent.pullbackComparison (𝒰.f i) c b rfl H).symm
      ((h𝒰 i).baseChange c)
  refine ⟨Spec B, b, hbflat, hblfp, ⟨z, ?_⟩,
    central_uniqueness_on_affine_chart hact b hdiag f g J hJ he hc⟩
  change 𝒰.f i (c z) = s
  rw [show c z = t from hz, ht]

/-- The exact arbitrary-ring, arbitrary-target central infinitesimal uniqueness assertion,
conditional only on the diagonalizable action-rigidity input. -/
theorem multiplicativeType_central_uniqueness_of_actionRigidity
    (hact : DiagonalizableActionRigidityInput.{u})
    (A : Type u) [CommRing A] (J : Ideal A) (hJ : IsNilpotent J)
    (G H : GroupScheme (Spec (CommRingCat.of A))) (f g : H ⟶ G)
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (he : (baseChange (Spec.algebraMap A (A ⧸ J))).map f =
      (baseChange (Spec.algebraMap A (A ⧸ J))).map g)
    (hc : IsCentral ((baseChange (Spec.algebraMap A (A ⧸ J))).map f)) : f = g :=
  central_uniqueness_over_commRingCat (R := CommRingCat.of A) hact J hJ G H f g hH he hc

end Langlands.GroupScheme.CentralInfinitesimalRigidity
