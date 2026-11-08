import Langlands.GroupScheme.SplitExistence.RootSubgroupRepresentation
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence

/-! # Opposite factor pairs in Chevalley groups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

section SL2

variable {R : Type*} [CommRing R]

/-- In `SL₂`, `[[1,0],[-s⁻¹,1]] [[1,s],[0,1]] [[1,0],[-s⁻¹,1]] = diag(s, s⁻¹) w`. -/
theorem sl2Lower_mul_sl2Upper_mul_sl2Lower (s : Rˣ) :
    sl2Lower (-((s⁻¹ : Rˣ) : R)) * sl2Upper (s : R) * sl2Lower (-((s⁻¹ : Rˣ) : R)) =
      sl2Diag s * sl2Weyl := by
  apply Subtype.ext
  change !![1, 0; -((s⁻¹ : Rˣ) : R), 1] * !![1, (s : R); 0, 1] * !![1, 0; -((s⁻¹ : Rˣ) : R), 1] =
    !![(s : R), 0; 0, ((s⁻¹ : Rˣ) : R)] * !![0, 1; -1, 0]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- In `SL₂`, `[[1,-t⁻¹],[0,1]] [[1,0],[t,1]] [[1,-t⁻¹],[0,1]] = diag(-t⁻¹, -t) w`. -/
theorem sl2Upper_mul_sl2Lower_mul_sl2Upper (t : Rˣ) :
    sl2Upper (-((t⁻¹ : Rˣ) : R)) * sl2Lower (t : R) * sl2Upper (-((t⁻¹ : Rˣ) : R)) =
      sl2Diag (-t⁻¹) * sl2Weyl := by
  apply Subtype.ext
  change !![1, -((t⁻¹ : Rˣ) : R); 0, 1] * !![1, 0; (t : R), 1] * !![1, -((t⁻¹ : Rˣ) : R); 0, 1] =
    !![((-t⁻¹ : Rˣ) : R), 0; 0, (((-t⁻¹)⁻¹ : Rˣ) : R)] * !![0, 1; -1, 0]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end SL2

/-- Inner automorphisms of a commutative group scheme are trivial. -/
theorem innerIso_hom_eq_id_of_comm {S : Scheme.{u}} (T : CommGroupScheme S)
    (y : Over.mk (𝟙 S) ⟶ T.toGrp.X) : (innerIso T.toGrp y).hom = 𝟙 T.toGrp := by
  apply hom_ext_points
  intro U x
  change x ≫ (innerIso T.toGrp y).hom.hom.hom = x ≫ 𝟙 T.toGrp.X
  rw [comp_innerIso_hom, Category.comp_id, mul_inv_cancel_comm]

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b)

section Ring

variable {R : Type u} [CommRing R]

/-- The torus character `μ ↦ s ^ ⟨μ, α^∨⟩` attached to a unit of a commutative ring and a
coroot. -/
def corootCharRing (j : J) (s : Rˣ) : Multiplicative X →* Rˣ where
  toFun x := s ^ P.toLinearMap (Multiplicative.toAdd x) (P.coroot j)
  map_one' := by simp
  map_mul' x y := by simp [_root_.zpow_add]

theorem φ_sl2Upper_ring (i : b.support) (s : R) : D.φ i R (sl2Upper s) = D.x i s :=
  Units.ext (D.φ_upper i R s)

theorem φ_sl2Lower_ring (i : b.support) (s : R) :
    D.φ i R (sl2Lower s) = D.x (P.reflectionPerm i i) s :=
  Units.ext (D.φ_lower i R s)

theorem φ_sl2Diag_ring (i : b.support) (s : Rˣ) :
    D.φ i R (sl2Diag s) = D.torusHom (corootCharRing (P := P) i s) := by
  apply Units.ext
  rw [D.φ_diag, coe_torusHom]
  rfl

/-- The opposite product of a simple root element is a torus element times the Weyl
element. -/
theorem x_opp_mul_x_mul_x_opp (i : b.support) (s : Rˣ) :
    D.x (P.reflectionPerm i i) (-((s⁻¹ : Rˣ) : R)) * D.x i (s : R) *
        D.x (P.reflectionPerm i i) (-((s⁻¹ : Rˣ) : R)) =
      D.torusHom (corootCharRing (P := P) i s) * D.φ i R sl2Weyl := by
  rw [← φ_sl2Lower_ring, ← φ_sl2Upper_ring, ← φ_sl2Diag_ring, ← map_mul, ← map_mul, ← map_mul,
    sl2Lower_mul_sl2Upper_mul_sl2Lower]

/-- The opposite product of a negative simple root element. -/
theorem x_mul_x_opp_mul_x (i : b.support) (t : Rˣ) :
    D.x i (-((t⁻¹ : Rˣ) : R)) * D.x (P.reflectionPerm i i) (t : R) * D.x i (-((t⁻¹ : Rˣ) : R)) =
      D.torusHom (corootCharRing (P := P) i (-t⁻¹)) * D.φ i R sl2Weyl := by
  rw [← φ_sl2Lower_ring, ← φ_sl2Upper_ring, ← φ_sl2Diag_ring, ← map_mul, ← map_mul, ← map_mul,
    sl2Upper_mul_sl2Lower_mul_sl2Upper]

/-- Conjugation by a simple Weyl element sends a root exponential to the exponential of the
reflected root, up to a sign chosen independently of the ring. -/
theorem exists_weyl_conj_x (i : b.support) (j : J) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (R : Type u) [CommRing R] (s : R),
      D.φ i R sl2Weyl * D.x j s * (D.φ i R sl2Weyl)⁻¹ =
        D.x (P.reflectionPerm i j) ((ε : R) * s) := by
  obtain ⟨ε, hε, h⟩ := D.weyl_conj i j
  exact ⟨ε, hε, fun R _ s => Units.ext (h R s)⟩

end Ring

omit D in
/-- The negative of the negative of a root is the root, as indices. -/
theorem reflectionPerm_neg_self (α : J) :
    P.reflectionPerm (P.reflectionPerm α α) (P.reflectionPerm α α) = α :=
  P.root.injective (by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
      RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, neg_neg])

omit D in
/-- Reflecting the negative of a root is the negative of the reflected root, as indices. -/
theorem reflectionPerm_reflectionPerm_neg (j α : J) :
    P.reflectionPerm j (P.reflectionPerm α α) =
      P.reflectionPerm (P.reflectionPerm j α) (P.reflectionPerm j α) :=
  P.root.injective (by
    have e1 : P.root (P.reflectionPerm α α) = - P.root α := by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    have e2 : P.root (P.reflectionPerm (P.reflectionPerm j α) (P.reflectionPerm j α)) =
        - P.root (P.reflectionPerm j α) := by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    rw [RootPairing.root_reflectionPerm, e1, e2, map_neg, RootPairing.root_reflectionPerm])

variable {D} {k : Type u} [Field k]

/-- An integral sign as a unit of the field. -/
def signUnit (ε : ℤˣ) : kˣ := Units.map (Int.castRingHom k).toMonoidHom ε

@[simp] theorem coe_signUnit (ε : ℤˣ) : ((signUnit ε : kˣ) : k) = ((ε : ℤ) : k) := rfl

theorem signUnit_mul_self (ε : ℤˣ) : (signUnit ε : kˣ) * signUnit ε = 1 := by
  rw [signUnit, ← map_mul, Int.units_mul_self, map_one]

namespace ChevGroup

variable (G : D.ChevGroup k)

/-- The rational root point with coordinate `s`. -/
def rootPt (j : J) (s : k) : rationalPoints G.H :=
  gaRationalEquiv k (Multiplicative.ofAdd s) ≫ (G.u j).hom.hom

theorem pointsEquiv_rootPt (j : J) (s : k) :
    GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) _ (G.rootPt j s ≫ G.i.hom.hom) =
      D.x j ((Scheme.ΓSpecIso (CommRingCat.of k)).inv s) := by
  rw [rootPt, Category.assoc, ← Grp.comp_hom_hom, G.u_comp, pointsEquiv_rootToGL,
    gaCoord_gaRationalEquiv]
  rfl

/-- The rational torus point attached to a character with values in the global units. -/
def torusPt (χ : Multiplicative X →* (Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤))ˣ) :
    rationalPoints G.H :=
  (torusPointsEquiv k _).symm χ ≫ G.t.hom.hom

theorem pointsEquiv_torusPt
    (χ : Multiplicative X →* (Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤))ˣ) :
    GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) _ (G.torusPt χ ≫ G.i.hom.hom) =
      D.torusHom χ := by
  rw [torusPt, Category.assoc, ← Grp.comp_hom_hom, G.t_comp, pointsEquiv_torusToGL,
    MulEquiv.apply_symm_apply]

theorem torusPt_mem_centralizerPoints
    (χ : Multiplicative X →* (Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤))ˣ) :
    G.torusPt χ ∈ centralizerPoints G.t := by
  rw [mem_centralizerPoints, torusPt, ← innerIso_hom_comp, innerIso_hom_eq_id_of_comm,
    Category.id_comp]

theorem weylPoint_mem_normalizerPoints (i : b.support) :
    G.weylPoint i ∈ normalizerPoints G.t :=
  ⟨_, G.isNormalizingPoint_weylPoint i⟩

/-- The opposite product of a nonidentity simple root point. -/
theorem rootPt_opp_mul_rootPt_mul_rootPt_opp (i : b.support) (S : kˣ) :
    G.rootPt (P.reflectionPerm i i) (-((S⁻¹ : kˣ) : k)) * G.rootPt i (S : k) *
        G.rootPt (P.reflectionPerm i i) (-((S⁻¹ : kˣ) : k)) =
      G.torusPt (corootCharRing (P := P) i
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom S)) *
        G.weylPoint i := by
  apply G.mono_i.right_cancellation
  apply (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) _).injective
  rw [MonObj.mul_comp, MonObj.mul_comp, MonObj.mul_comp, map_mul, map_mul, map_mul,
    pointsEquiv_rootPt, pointsEquiv_rootPt, pointsEquiv_torusPt, pointsEquiv_weylPoint,
    ← D.x_opp_mul_x_mul_x_opp]
  simp only [map_neg, Units.coe_map, Units.coe_map_inv, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]

/-- The opposite product of a nonidentity negative simple root point. -/
theorem rootPt_mul_rootPt_opp_mul_rootPt (i : b.support) (S : kˣ) :
    G.rootPt i (-((S⁻¹ : kˣ) : k)) * G.rootPt (P.reflectionPerm i i) (S : k) *
        G.rootPt i (-((S⁻¹ : kˣ) : k)) =
      G.torusPt (corootCharRing (P := P) i
        (-(Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom S)⁻¹)) *
        G.weylPoint i := by
  apply G.mono_i.right_cancellation
  apply (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) _).injective
  rw [MonObj.mul_comp, MonObj.mul_comp, MonObj.mul_comp, map_mul, map_mul, map_mul,
    pointsEquiv_rootPt, pointsEquiv_rootPt, pointsEquiv_torusPt, pointsEquiv_weylPoint,
    ← D.x_mul_x_opp_mul_x]
  simp only [map_neg, Units.coe_map, Units.coe_map_inv, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]

/-- Conjugation by a simple Weyl point moves rational root points by a sign. -/
theorem exists_weylPoint_conj_rootPt (i : b.support) (j : J) :
    ∃ ε : ℤˣ, ∀ s : k, G.weylPoint i * G.rootPt j s * (G.weylPoint i)⁻¹ =
      G.rootPt (P.reflectionPerm i j) (((ε : ℤ) : k) * s) := by
  obtain ⟨ε, hε, h⟩ := D.exists_weyl_conj_x i j
  have hu : ∃ u : ℤˣ, (u : ℤ) = ε := by
    rcases hε with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨-1, rfl⟩
  obtain ⟨u, rfl⟩ := hu
  refine ⟨u, fun s => ?_⟩
  apply G.mono_i.right_cancellation
  apply (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) _).injective
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, map_mul, map_mul, map_inv,
    pointsEquiv_weylPoint, pointsEquiv_rootPt, pointsEquiv_rootPt, h, map_mul, map_intCast]

/-- The rational opposite product property of a root. -/
def OppositeRootProperty (α : J) : Prop :=
  ∀ S : kˣ, ∃ ε : ℤˣ,
    G.rootPt (P.reflectionPerm α α) (((ε : ℤ) : k) * ((S⁻¹ : kˣ) : k)) * G.rootPt α (S : k) *
        G.rootPt (P.reflectionPerm α α) (((ε : ℤ) : k) * ((S⁻¹ : kˣ) : k)) ∈
      normalizerPoints G.t

theorem oppositeRootProperty_simple (i : b.support) : G.OppositeRootProperty i := by
  intro S
  refine ⟨-1, ?_⟩
  have h := G.rootPt_opp_mul_rootPt_mul_rootPt_opp i S
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
  rw [h]
  exact (normalizerPoints G.t).mul_mem
    (centralizerPoints_le_normalizerPoints G.t (G.torusPt_mem_centralizerPoints _))
    (G.weylPoint_mem_normalizerPoints i)

theorem oppositeRootProperty_neg_simple (i : b.support) :
    G.OppositeRootProperty (P.reflectionPerm i i) := by
  intro S
  refine ⟨-1, ?_⟩
  have h := G.rootPt_mul_rootPt_opp_mul_rootPt i S
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
  rw [reflectionPerm_neg_self, h]
  exact (normalizerPoints G.t).mul_mem
    (centralizerPoints_le_normalizerPoints G.t (G.torusPt_mem_centralizerPoints _))
    (G.weylPoint_mem_normalizerPoints i)

theorem oppositeRootProperty_reflect {α : J} (h : G.OppositeRootProperty α) (j : b.support) :
    G.OppositeRootProperty (P.reflectionPerm j α) := by
  intro S
  obtain ⟨ε₁, h₁⟩ := G.exists_weylPoint_conj_rootPt j α
  obtain ⟨ε₂, h₂⟩ := G.exists_weylPoint_conj_rootPt j (P.reflectionPerm α α)
  obtain ⟨ε, hm⟩ := h (signUnit ε₁ * S)
  refine ⟨ε₂ * ε * ε₁, ?_⟩
  have hn := G.weylPoint_mem_normalizerPoints j
  have hconj := (normalizerPoints G.t).mul_mem
    ((normalizerPoints G.t).mul_mem hn hm) ((normalizerPoints G.t).inv_mem hn)
  have hexp : ∀ a c : rationalPoints G.H, G.weylPoint j * (a * c * a) * (G.weylPoint j)⁻¹ =
      (G.weylPoint j * a * (G.weylPoint j)⁻¹) * (G.weylPoint j * c * (G.weylPoint j)⁻¹) *
        (G.weylPoint j * a * (G.weylPoint j)⁻¹) := by
    intro a c
    group
  have hc1 : ((ε₁ : ℤ) : k) * ((signUnit ε₁ * S : kˣ) : k) = (S : k) := by
    rcases Int.units_eq_one_or ε₁ with rfl | rfl <;> simp [signUnit]
  have hc2 : ((ε₂ : ℤ) : k) * (((ε : ℤ) : k) * (((signUnit ε₁ * S)⁻¹ : kˣ) : k)) =
      (((ε₂ * ε * ε₁ : ℤˣ) : ℤ) : k) * ((S⁻¹ : kˣ) : k) := by
    rcases Int.units_eq_one_or ε₁ with rfl | rfl <;>
      rcases Int.units_eq_one_or ε₂ with rfl | rfl <;>
      rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [signUnit]
  rw [hexp, h₁, h₂, reflectionPerm_reflectionPerm_neg, hc1, hc2] at hconj
  exact hconj

/-- Every root and its negative have the rational opposite product property. -/
theorem oppositeRootProperty_all [Finite J] [P.IsReduced] (α : J) :
    G.OppositeRootProperty α ∧ G.OppositeRootProperty (P.reflectionPerm α α) :=
  b.induction_reflect
    (p := fun β => G.OppositeRootProperty β ∧ G.OppositeRootProperty (P.reflectionPerm β β)) α
    (fun β h => ⟨h.2, by rw [reflectionPerm_neg_self]; exact h.1⟩)
    (fun i hi => ⟨G.oppositeRootProperty_simple ⟨i, hi⟩,
      G.oppositeRootProperty_neg_simple ⟨i, hi⟩⟩)
    (fun β j h hj => ⟨G.oppositeRootProperty_reflect h.1 ⟨j, hj⟩, by
      rw [← reflectionPerm_reflectionPerm_neg]
      exact G.oppositeRootProperty_reflect h.2 ⟨j, hj⟩⟩)

theorem rootPt_zero (j : J) : G.rootPt j 0 = 1 := by
  rw [rootPt, ofAdd_zero, map_one]
  exact MonObj.one_comp _

omit [Field k] in
theorem charOf_root_reflectionPerm_self [Field k] (j : J) :
    charOf k (P.root (P.reflectionPerm j j)) = -charOf k (P.root j) := by
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, ← charOfHom_apply,
    map_neg, charOfHom_apply]

variable [Finite J] [P.IsReduced] [Module.Finite ℤ X] [Module.Free ℤ X]
  [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom]

theorem rootPt_mem (j : J) (s : k) :
    G.rootPt j s ∈ (RelativeRoot.subgroup G.t (charOf k (P.root j))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
  (G.rootCoordEquiv j (Multiplicative.ofAdd s)).property

omit [Module.Finite ℤ X] [Module.Free ℤ X] [IsAffine G.H.X.left]
  [LocallyOfFiniteType G.H.X.hom] in
/-- The negative root points form the negative root subgroup. -/
theorem rootPt_mem_neg [Module.Finite ℤ X] [Module.Free ℤ X] [IsAffine G.H.X.left]
    [LocallyOfFiniteType G.H.X.hom] (j : J) (t : k) :
    G.rootPt (P.reflectionPerm j j) t ∈
      (RelativeRoot.subgroup G.t (-charOf k (P.root j))).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  rw [← charOf_root_reflectionPerm_self]
  exact G.rootPt_mem _ t

/-- The explicit opposite factor pair of a nonidentity root point. -/
theorem exists_isOppositeFactorPair_rootPt [IsAffineHom G.H.X.hom] [Mono G.t.hom.hom.left]
    (j : J) (S : kˣ) :
    ∃ ε : ℤˣ, RelativeRoot.IsOppositeFactorPair G.t (charOf k (P.root j)) (G.rootPt j (S : k))
      (G.rootPt (P.reflectionPerm j j) (((ε : ℤ) : k) * ((S⁻¹ : kˣ) : k)),
        G.rootPt (P.reflectionPerm j j) (((ε : ℤ) : k) * ((S⁻¹ : kˣ) : k))) := by
  obtain ⟨ε, hm⟩ := (G.oppositeRootProperty_all j).1 S
  exact ⟨ε, G.rootPt_mem_neg j _, G.rootPt_mem_neg j _, hm⟩

/-- **Opposite factor pairs in Chevalley groups.** Every nonidentity rational point of a
root subgroup has an explicit opposite pair whose product normalizes the torus. -/
theorem hasOppositeFactorPairs [IsAffineHom G.H.X.hom] [Mono G.t.hom.hom.left] :
    RelativeRoot.HasOppositeFactorPairs G.t := by
  intro a ha x hx hx1
  have ha' : a ∈ roots G.t := ha
  rw [G.roots_t] at ha'
  obtain ⟨j, rfl⟩ := ha'
  obtain ⟨s, hs⟩ := (G.rootCoordEquiv j).surjective ⟨x, hx⟩
  have hxs : x = G.rootPt j (Multiplicative.toAdd s) := (congrArg Subtype.val hs).symm
  have hs0 : Multiplicative.toAdd s ≠ 0 := by
    intro h0
    apply hx1
    rw [hxs, h0, rootPt_zero]
  obtain ⟨ε, hp⟩ := G.exists_isOppositeFactorPair_rootPt j (Units.mk0 _ hs0)
  rw [hxs]
  exact ⟨_, hp⟩

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
