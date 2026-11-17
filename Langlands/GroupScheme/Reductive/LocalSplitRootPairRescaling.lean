import Langlands.GroupScheme.Reductive.LocalSplitRootPairLaws

/-! # Inverse-unit rescaling of Weyl-normalized root pairs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.LocalSplitCell

section Ring

variable {R : Type u} [CommRing R]
  {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {alpha nu : I → ℤ} {xp xm : Ga R ⟶ G}

/-- The unit-denominator law controls rescaling even when the difference
of the scaling unit from one is not invertible. -/
theorem RankOneLaws.rescale_relation (h : RankOneLaws i nu xp xm)
    (hm : IsRootParametrization i (-alpha) xm)
    (hpair : coPairing alpha nu = 2)
    (Z : Over (Spec (CommRingCat.of R))) (q : Γ(Z.left, ⊤)ˣ) :
    (cocharPoint nu Z q ≫ i.hom.hom) *
        (rootPoint xm Z (-(q : Γ(Z.left, ⊤))) *
          (rootPoint xp Z (↑q⁻¹ : Γ(Z.left, ⊤)) *
            rootPoint xm Z (-(q : Γ(Z.left, ⊤))))) =
      G.constantPoint (weylPoint xp xm) Z := by
  let A := rootPoint xp Z
  let B := rootPoint xm Z
  let H := cocharPoint nu Z q ≫ i.hom.hom
  have hrel := h.2.2.2 Z 1 ((q : Γ(Z.left, ⊤)) - 1) q (by ring)
  change A 1 * B ((q : Γ(Z.left, ⊤)) - 1) =
    B ((↑q⁻¹ : Γ(Z.left, ⊤)) * ((q : Γ(Z.left, ⊤)) - 1)) *
      H * A ((↑q⁻¹ : Γ(Z.left, ⊤)) * 1) at hrel
  rw [mul_one] at hrel
  have hneg : coPairing (-alpha) nu = -2 := by
    simpa only [coPairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] using
      congrArg Neg.neg hpair
  have hval :
      VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
        (splitTorus.exponentCharacter _ I (-alpha)) Z (cocharPoint nu Z q) =
        (↑q⁻¹ : Γ(Z.left, ⊤)) * (↑q⁻¹ : Γ(Z.left, ⊤)) := by
    change torusChar (-alpha) Z (cocharPoint nu Z q) = _
    rw [torusChar_cocharPoint, hneg,
      show q ^ (-2 : ℤ) = q⁻¹ * q⁻¹ by group, Units.val_mul]
  have hweight : H * B (-(q : Γ(Z.left, ⊤))) =
      B (-(↑q⁻¹ : Γ(Z.left, ⊤))) * H := by
    have he := hm.equivariant Z (cocharPoint nu Z q) (-(q : Γ(Z.left, ⊤)))
    rw [hval] at he
    have hc :
        ((↑q⁻¹ : Γ(Z.left, ⊤)) * (↑q⁻¹ : Γ(Z.left, ⊤))) *
          (-(q : Γ(Z.left, ⊤))) = -(↑q⁻¹ : Γ(Z.left, ⊤)) := by
      linear_combination -(↑q⁻¹ : Γ(Z.left, ⊤)) * Units.inv_mul q
    rw [hc] at he
    exact (mul_inv_eq_iff_eq_mul).mp he
  have hshift :
      -1 + (↑q⁻¹ : Γ(Z.left, ⊤)) * ((q : Γ(Z.left, ⊤)) - 1) =
        -(↑q⁻¹ : Γ(Z.left, ⊤)) := by
    linear_combination Units.inv_mul q
  calc
    _ = B (-(↑q⁻¹ : Γ(Z.left, ⊤))) *
        (H * A (↑q⁻¹ : Γ(Z.left, ⊤))) *
          B (-(q : Γ(Z.left, ⊤))) := by
      change H * (B _ * (A _ * B _)) = _
      rw [← mul_assoc, ← mul_assoc, hweight]
      simp only [mul_assoc]
    _ = B (-1) *
        (B ((↑q⁻¹ : Γ(Z.left, ⊤)) * ((q : Γ(Z.left, ⊤)) - 1)) *
          (H * A (↑q⁻¹ : Γ(Z.left, ⊤)))) *
            B (-(q : Γ(Z.left, ⊤))) := by
      rw [← hshift]
      change rootPoint xm Z _ * _ * _ = _
      rw [rootPoint_add]
      simp only [B, mul_assoc]
    _ = B (-1) * (A 1 * B ((q : Γ(Z.left, ⊤)) - 1)) *
        B (-(q : Γ(Z.left, ⊤))) := by
      rw [mul_assoc] at hrel
      rw [← hrel]
    _ = G.constantPoint (weylPoint xp xm) Z := by
      rw [constantPoint_weylPoint]
      simp only [A, B, mul_assoc]
      rw [← rootPoint_add]
      congr 2
      congr 1
      ring

/-- Rescaling the two supplied roots by inverse units preserves any
prescribed Weyl action compatible with the rank-one laws. -/
theorem RankOneLaws.isWeylPoint_rescale [DecidableEq I]
    (h : RankOneLaws i nu xp xm)
    (hm : IsRootParametrization i (-alpha) xm)
    (hpair : coPairing alpha nu = 2)
    {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (hn : IsWeylPoint i (weylPoint xp xm) f) (kappa : Rˣ) :
    IsWeylPoint i
      (weylPoint (scaleHom (kappa : R) ≫ xp)
        (scaleHom ((kappa⁻¹ : Rˣ) : R) ≫ xm)) f := by
  intro Z t
  let q : Γ(Z.left, ⊤)ˣ := Units.map (baseScalar Z).toMonoidHom kappa⁻¹
  let H := cocharPoint nu Z q ≫ i.hom.hom
  let n := weylPoint (scaleHom (kappa : R) ≫ xp)
    (scaleHom ((kappa⁻¹ : Rˣ) : R) ≫ xm)
  have hq : (q : Γ(Z.left, ⊤)) = baseScalar Z (kappa⁻¹ : Rˣ) := rfl
  have hqinv : (↑q⁻¹ : Γ(Z.left, ⊤)) = baseScalar Z (kappa : R) := by
    simp only [q, map_inv, inv_inv]
    rfl
  have hs : G.constantPoint n Z =
      rootPoint xm Z (-(q : Γ(Z.left, ⊤))) *
        (rootPoint xp Z (↑q⁻¹ : Γ(Z.left, ⊤)) *
          rootPoint xm Z (-(q : Γ(Z.left, ⊤)))) := by
    simp only [n, constantPoint_weylPoint, rootPoint_scaleHom,
      mul_neg_one, mul_one, hq, hqinv, mul_assoc]
  have hr : H * G.constantPoint n Z = G.constantPoint (weylPoint xp xm) Z := by
    rw [hs]
    exact h.rescale_relation hm hpair Z q
  have he := hn Z t
  simp only [toUnit_comp_eq_constantPoint] at he ⊢
  change G.constantPoint n Z * (t ≫ i.hom.hom) * (G.constantPoint n Z)⁻¹ = _
  have hc :
      H * (t ≫ (splitTorus.exponentIso _ I f).hom.hom.hom ≫ i.hom.hom) =
        (t ≫ (splitTorus.exponentIso _ I f).hom.hom.hom ≫ i.hom.hom) * H := by
    simpa only [Category.assoc] using
      torus_comp_mul_comm i
        (t ≫ (splitTorus.exponentIso _ I f).hom.hom.hom)
        (cocharPoint nu Z q)
  calc
    _ = H⁻¹ *
        (G.constantPoint (weylPoint xp xm) Z * (t ≫ i.hom.hom) *
          (G.constantPoint (weylPoint xp xm) Z)⁻¹) * H := by
      rw [← hr]
      group
    _ = H⁻¹ *
        (t ≫ (splitTorus.exponentIso _ I f).hom.hom.hom ≫ i.hom.hom) * H := by rw [he]
    _ = _ := by rw [mul_assoc, ← hc, inv_mul_cancel_left]

end Ring

section Local

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- For every root over an arbitrary local ring, inverse-unit rescaling
of an actual normalized opposite pair retains the prescribed reflection. -/
theorem isWeylPoint_rescale (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
    {xp xm : Ga R ⟶ G}
    (hp : IsRootParametrization i (P.root a) xp)
    (hm : IsRootParametrization i (-P.root a) xm)
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a)) (kappa : Rˣ) :
    IsWeylPoint i
      (weylPoint (scaleHom (kappa : R) ≫ xp)
        (scaleHom ((kappa⁻¹ : Rˣ) : R) ≫ xm)) (P.reflection a) := by
  have h := localSplitRootPairLaws R G hG I i hi hmax J P hP a xp xm hp hm hn
  apply h.isWeylPoint_rescale hm _ hn kappa
  rw [coPairing, ← hP.pairing (IsLocalRing.ResidueField R), P.root_coroot_two]

end Local

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme

open LocalSplitCell

/-- Inverse-unit rescaling of an actual Weyl-normalized root pair
preserves its reflection over any local ring. -/
def LocalSplitRootPairRescalingStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] [DecidableEq I]
      (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
        IsFibrewiseRootDatumOf I G i P →
        ∀ (a : J) (xp xm : Ga R ⟶ G),
          IsRootParametrization i (P.root a) xp →
          IsRootParametrization i (-P.root a) xm →
          IsWeylPoint i (weylPoint xp xm) (P.reflection a) →
          ∀ kappa : Rˣ,
            IsWeylPoint i
              (weylPoint (scaleHom (kappa : R) ≫ xp)
                (scaleHom ((kappa⁻¹ : Rˣ) : R) ≫ xm)) (P.reflection a)

/-- The supplied-root laws and the coroot pairing establish rescaling
for every root over an arbitrary local ring. -/
theorem localSplitRootPairRescaling : LocalSplitRootPairRescalingStatement.{u} := by
  intro R _ _ G _ hG I _ _ i hi hmax J P hP a xp xm hp hm hn kappa
  exact isWeylPoint_rescale hG hi hmax hP a hp hm hn kappa

end Langlands.GroupScheme
