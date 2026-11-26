import Langlands.GroupScheme.Commutative.MultiplicativeUnipotentSplitting
import Langlands.GroupScheme.SimplyConnected.SplitPicardCharacterLifting
import Mathlib.Tactic.Abel

/-! # Scalar cocycles on commutative affine group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A natural scalar two-cocycle on the actual group of points on every test scheme. -/
structure UnitTwoCocycle {S : Scheme.{u}} (H : GroupScheme S) where
  value : ∀ {T : Over S}, (T ⟶ H.X) → (T ⟶ H.X) → Γ(T.left, ⊤)ˣ
  precomp : ∀ {T U : Over S} (a : U ⟶ T) (x y : T ⟶ H.X),
    value (a ≫ x) (a ≫ y) = Units.map a.left.appTop.hom.toMonoidHom (value x y)
  cocycle : ∀ {T : Over S} (x y z : T ⟶ H.X),
    value x y * value (x * y) z = value y z * value x (y * z)

namespace UnitTwoCocycle

section General

variable {S : Scheme.{u}} {H : GroupScheme S} (c : UnitTwoCocycle H)

private lemma one_left {T : Over S} (x : T ⟶ H.X) : c.value 1 x = c.value 1 1 := by
  have h := c.cocycle 1 1 x
  simp only [one_mul] at h
  exact (mul_right_cancel h).symm

private lemma one_right {T : Over S} (x : T ⟶ H.X) : c.value x 1 = c.value 1 1 := by
  have h := c.cocycle x 1 1
  simp only [mul_one] at h
  exact mul_right_cancel h

private def normalized : UnitTwoCocycle H where
  value x y := c.value x y / c.value 1 1
  precomp a x y := by rw [map_div, c.precomp, ← c.precomp a 1 1, MonObj.comp_one]
  cocycle x y z := by
    simp only [div_mul_div_comm, c.cocycle]

private lemma normalized_one_left {T : Over S} (x : T ⟶ H.X) :
    c.normalized.value 1 x = 1 := by simp [normalized, c.one_left]

private lemma normalized_one_right {T : Over S} (x : T ⟶ H.X) :
    c.normalized.value x 1 = 1 := by simp [normalized, c.one_right]

variable [IsCommMonObj H.X]

private lemma commutator_mul {T : Over S} (x y z : T ⟶ H.X) :
    c.value (x * y) z / c.value z (x * y) =
      (c.value x z / c.value z x) * (c.value y z / c.value z y) := by
  have h1 : c.value (x * y) z = c.value y z * c.value x (y * z) / c.value x y :=
    eq_div_iff_mul_eq'.mpr (by rw [mul_comm, c.cocycle])
  have h2 : c.value z (x * y) = c.value z x * c.value (z * x) y / c.value x y :=
    eq_div_iff_mul_eq'.mpr (by rw [mul_comm, ← c.cocycle])
  have h3 : c.value x (y * z) = c.value x z * c.value (z * x) y / c.value z y :=
    eq_div_iff_mul_eq'.mpr (by
      rw [mul_comm y z, mul_comm z x, mul_comm (c.value x (z * y))]
      exact (c.cocycle x z y).symm)
  rw [h1, h2, h3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

/-- The power of the scalar cocycle has trivial commutator if that power kills the group. -/
lemma pow_value_comm (n : ℕ) (h : ∀ {T : Over S} (x : T ⟶ H.X), x ^ n = 1)
    {T : Over S} (x y : T ⟶ H.X) : c.value x y ^ n = c.value y x ^ n := by
  let f : (T ⟶ H.X) →* Γ(T.left, ⊤)ˣ :=
    MonoidHom.mk' (fun x => c.value x y / c.value y x) (fun x z => c.commutator_mul x z y)
  have hf : f (x ^ n) = 1 := by rw [h, map_one]
  rw [map_pow] at hf
  exact div_eq_one.mp (by simpa only [f, MonoidHom.mk'_apply, div_pow] using hf)

/-- A scalar cocycle raised pointwise to a nonnegative power. -/
def power (n : ℕ) : UnitTwoCocycle H where
  value x y := c.value x y ^ n
  precomp a x y := by rw [map_pow, c.precomp]
  cocycle x y z := by rw [← mul_pow, ← mul_pow, c.cocycle]

/-- A global unit on the group giving a coboundary formula on every test scheme. -/
def HasCorrection : Prop :=
  ∃ b : Γ(H.X.left, ⊤)ˣ, ∀ (T : Over S) (x y : T ⟶ H.X),
    Units.map (x * y).left.appTop.hom.toMonoidHom b =
      Units.map x.left.appTop.hom.toMonoidHom b *
        Units.map y.left.appTop.hom.toMonoidHom b * c.value x y

private structure SymmetricNormalized (H : GroupScheme S) extends UnitTwoCocycle H where
  oneLeft : ∀ {T : Over S} (x : T ⟶ H.X), value 1 x = 1
  oneRight : ∀ {T : Over S} (x : T ⟶ H.X), value x 1 = 1
  comm : ∀ {T : Over S} (x y : T ⟶ H.X), value x y = value y x

namespace SymmetricNormalized

variable (d : SymmetricNormalized H)

@[nolint unusedArguments]
private def Points (_ : SymmetricNormalized H) (T : Over S) := (T ⟶ H.X) × Γ(T.left, ⊤)ˣ

private def pointMul {T : Over S} (x y : Points d T) : Points d T :=
  (x.1 * y.1, x.2 * y.2 * d.value x.1 y.1)

private def pointOne (T : Over S) : Points d T := (1, 1)

private instance pointsCommGroup (T : Over S) : CommGroup (Points d T) where
  mul := d.pointMul
  one := d.pointOne T
  inv x := (x.1⁻¹, x.2⁻¹ * (d.value x.1⁻¹ x.1)⁻¹)
  mul_assoc x y z := by
    apply Prod.ext
    · exact mul_assoc _ _ _
    · change x.2 * y.2 * d.value x.1 y.1 * z.2 * d.value (x.1 * y.1) z.1 =
        x.2 * (y.2 * z.2 * d.value y.1 z.1) * d.value x.1 (y.1 * z.1)
      calc
        _ = (x.2 * y.2 * z.2) * (d.value x.1 y.1 * d.value (x.1 * y.1) z.1) := by ac_rfl
        _ = _ := by rw [d.cocycle]; ac_rfl
  one_mul x := by
    apply Prod.ext
    · exact one_mul _
    · change 1 * x.2 * d.value 1 x.1 = x.2
      rw [d.oneLeft, one_mul, mul_one]
  mul_one x := by
    apply Prod.ext
    · exact mul_one _
    · change x.2 * 1 * d.value x.1 1 = x.2
      rw [d.oneRight, mul_one, mul_one]
  inv_mul_cancel x := by
    apply Prod.ext
    · exact inv_mul_cancel _
    · change x.2⁻¹ * (d.value x.1⁻¹ x.1)⁻¹ * x.2 * d.value x.1⁻¹ x.1 = 1
      rw [mul_right_comm _ _ x.2, inv_mul_cancel, one_mul, inv_mul_cancel]
  mul_comm x y := by
    apply Prod.ext
    · exact mul_comm _ _
    · change x.2 * y.2 * d.value x.1 y.1 = y.2 * x.2 * d.value y.1 x.1
      rw [mul_comm x.2 y.2, d.comm x.1 y.1]

private def restrictPoint {T U : Over S} (a : U ⟶ T) : Points d T →* Points d U where
  toFun x := (a ≫ x.1, Units.map a.left.appTop.hom.toMonoidHom x.2)
  map_one' := Prod.ext (MonObj.comp_one a) (map_one _)
  map_mul' x y := by
    apply Prod.ext
    · exact MonObj.comp_mul a x.1 y.1
    · change Units.map a.left.appTop.hom.toMonoidHom (x.2 * y.2 * d.value x.1 y.1) =
        Units.map a.left.appTop.hom.toMonoidHom x.2 *
          Units.map a.left.appTop.hom.toMonoidHom y.2 * d.value (a ≫ x.1) (a ≫ y.1)
      simp only [d.precomp, map_mul]

private def pointsFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (Points d T.unop)
  map a := CommGrpCat.ofHom (d.restrictPoint a.unop)
  map_id T := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Prod.ext
    · exact Category.id_comp _
    · apply Units.ext
      change (𝟙 T.unop.left : T.unop.left ⟶ T.unop.left).appTop _ = _
      rw [Scheme.Hom.id_appTop]
      rfl
  map_comp a b := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Prod.ext
    · exact Category.assoc _ _ _
    · apply Units.ext
      rfl

private abbrev extensionObject := H.X ⊗ (Gm S).X

private def extensionRepresentation :
    (d.pointsFunctor ⋙ forget _).RepresentableBy (extensionObject (H := H)) where
  homEquiv {T} :=
    { toFun := fun x => (x ≫ fst _ _, Gm.pointsEquiv S T (x ≫ snd _ _))
      invFun := fun x => lift x.1 ((Gm.pointsEquiv S T).symm x.2)
      left_inv := fun x => by
        change lift (x ≫ fst _ _) ((Gm.pointsEquiv S T).symm
          (Gm.pointsEquiv S T (x ≫ snd _ _))) = x
        rw [MulEquiv.symm_apply_apply, lift_comp_fst_snd]
      right_inv := fun x => Prod.ext (lift_fst _ _)
        (by
          change Gm.pointsEquiv S T (lift x.1 ((Gm.pointsEquiv S T).symm x.2) ≫ snd _ _) = x.2
          rw [lift_snd, MulEquiv.apply_symm_apply]) }
  homEquiv_comp a x := by
    apply Prod.ext
    · exact Category.assoc _ _ _
    · change Gm.pointsEquiv S _ ((a ≫ x) ≫ snd _ _) = _
      rw [Category.assoc, Gm.pointsEquiv_naturality]
      rfl

private def extension : CommGroupScheme S :=
  letI g : GrpObj (extensionObject (H := H)) :=
    GrpObj.ofRepresentableBy _ (d.pointsFunctor ⋙ forget₂ CommGrpCat GrpCat) d.extensionRepresentation
  { toGrp := { X := extensionObject (H := H), grp := g }
    comm := IsCommMonObj.ofRepresentableBy _ (d.pointsFunctor ⋙ forget₂ CommGrpCat CommMonCat)
      d.extensionRepresentation }

set_option maxHeartbeats 900000 in
private def pointEquiv (T : Over S) : (T ⟶ d.extension.X) ≃* Points d T :=
  ((yonedaGrpObjIsoOfRepresentableBy d.extension.X (d.pointsFunctor ⋙ forget₂ CommGrpCat GrpCat)
    d.extensionRepresentation).app (op T)).groupIsoToMulEquiv

private lemma pointEquiv_apply {T : Over S} (x : T ⟶ d.extension.X) :
    d.pointEquiv T x = (x ≫ fst _ _, Gm.pointsEquiv S T (x ≫ snd _ _)) := rfl

private lemma pointEquiv_mul {T : Over S} (x y : T ⟶ d.extension.X) :
    d.pointEquiv T (x * y) = d.pointMul (d.pointEquiv T x) (d.pointEquiv T y) :=
  map_mul (d.pointEquiv T) x y

private def inclusionPoints (T : Over S) : (T ⟶ (Gm S).X) →* (T ⟶ d.extension.X) :=
  MonoidHom.mk' (fun t => lift 1 t) fun x y => by
    apply (d.pointEquiv T).injective
    rw [d.pointEquiv_mul]
    simp [pointEquiv_apply, pointMul, d.oneLeft]

private lemma inclusionPoints_naturality {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ (Gm S).X) :
    d.inclusionPoints T' (a ≫ x) = a ≫ d.inclusionPoints T x := by
  change lift 1 (a ≫ x) = a ≫ lift 1 x
  rw [comp_lift, MonObj.comp_one]

private def inclusion : (Gm S).toGrp ⟶ d.extension.toGrp :=
  homOfPoints d.inclusionPoints d.inclusionPoints_naturality

private lemma inclusion_hom : d.inclusion.hom.hom = lift 1 (𝟙 _) := by
  have h := comp_homOfPoints d.inclusionPoints d.inclusionPoints_naturality (Gm S).X (𝟙 _)
  rw [Category.id_comp] at h
  exact h

end SymmetricNormalized

end General

section Field

variable {K : Type u} [Field K] [IsAlgClosed K]

private theorem gm_retract {G : CommGroupScheme (Spec (CommRingCat.of K))} [IsAffine G.X.left]
    (i : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ G.toGrp) (hi : IsClosedSubgroup i) :
    ∃ r : G.toGrp ⟶ (Gm (Spec (CommRingCat.of K))).toGrp, i ≫ r = 𝟙 _ := by
  let R := CommRingCat.of K
  let N := PUnit.{u+1} → ℤ
  let A := AffineCoordinates.hopfAlgebra G.toGrp
  let eG := AffineCoordinates.hopfSpecIso G.toGrp
  let eZ : (hopfSpec (CommRingCat.of K)).obj (op (Diagonalizable.hopfAlgebra R N)) ≅ (Gm (Spec (CommRingCat.of K))).toGrp :=
    Diagonalizable.hopfSpecIso R N ≪≫ (SplitPicardCharacterLifting.gmIso R).symm
  let π : A ⟶ Diagonalizable.hopfAlgebra R N :=
    (hopfSpec.fullyFaithful.preimage (eZ.hom ≫ i ≫ eG.inv)).unop
  have hπ : (hopfSpec (CommRingCat.of K)).map π.op = eZ.hom ≫ i ≫ eG.inv :=
    hopfSpec.fullyFaithful.map_preimage _
  have hi' : IsClosedSubgroup ((hopfSpec (CommRingCat.of K)).map π.op) := by
    rw [hπ]
    exact IsClosedSubgroup.iso_comp eZ (hi.comp_iso eG.symm)
  have hsurj : Function.Surjective π.hom :=
    CentralExtensionHopfSpec.surjective_of_isClosedSubgroup π hi'
  have : Coalgebra.IsCocomm K A := AffineCoordinates.hopfAlgebra_isCocomm G.toGrp
  obtain ⟨g, hg⟩ := CommutativeDecomposition.degree_surjective π.hom hsurj (fun _ => 1 : N)
  let e := SplitPicardCharacterLifting.degreeHom g
  have he (n : N) : CentralDiagonalizableExtensionHopf.degree π.hom (e n) = n := by
    change CentralDiagonalizableExtensionHopf.degree π.hom (n PUnit.unit • g) = n
    rw [map_zsmul, hg]
    funext x
    cases x
    change n PUnit.unit * 1 = n PUnit.unit
    exact mul_one _
  let ψ : Diagonalizable.hopfAlgebra R N ⟶ A :=
    CommHopfAlgCat.ofHom (CommutativeDecomposition.sectionHom e)
  have hψπ : ψ ≫ π = 𝟙 _ := CommHopfAlgCat.hom_ext
    (CommutativeDecomposition.comp_sectionHom π.hom e he)
  have hzπ : i ≫ eG.inv = eZ.inv ≫ (hopfSpec (CommRingCat.of K)).map π.op := by rw [hπ]; simp
  refine ⟨eG.inv ≫ (hopfSpec (CommRingCat.of K)).map ψ.op ≫ eZ.hom, ?_⟩
  rw [← Category.assoc, hzπ, Category.assoc, ← Functor.map_comp_assoc, ← op_comp, hψπ]
  simp

variable {H : GroupScheme (Spec (CommRingCat.of K))} [IsCommMonObj H.X] [IsAffineHom H.X.hom]
  (c : UnitTwoCocycle H)

set_option maxHeartbeats 1200000 in
private theorem exists_correction_of_normalized (d : SymmetricNormalized H) :
    d.toUnitTwoCocycle.HasCorrection := by
  unfold HasCorrection
  let E := d.extension
  let i := d.inclusion
  have : IsAffineHom (Gm (Spec (CommRingCat.of K))).X.hom := isSplitTorus_gm.isAffineHom
  have : IsAffine (Gm (Spec (CommRingCat.of K))).X.left :=
    isAffine_of_isAffineHom (Gm (Spec (CommRingCat.of K))).X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsAffine E.X.left :=
    inferInstanceAs (IsAffine (pullback H.X.hom (Gm (Spec (CommRingCat.of K))).X.hom))
  have hi : IsClosedSubgroup i := by
    apply IsClosedImmersion.of_surjective_of_isAffine
    let s : E.X ⟶ (Gm (Spec (CommRingCat.of K))).X := snd _ _
    have hs : i.hom.hom ≫ s = 𝟙 _ := by
      change d.inclusion.hom.hom ≫ snd _ _ = 𝟙 _
      rw [d.inclusion_hom, lift_snd]
    intro r
    refine ⟨s.left.appTop r, ?_⟩
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left, hs,
      Over.id_left, Scheme.Hom.id_appTop]
    rfl
  obtain ⟨r, hr⟩ := gm_retract i hi
  let t : H.X ⟶ E.X := lift (𝟙 _) 1
  let b := (Gm.pointsEquiv (Spec (CommRingCat.of K)) H.X (t ≫ r.hom.hom))⁻¹
  refine ⟨b, fun T x y => ?_⟩
  let G := (Gm (Spec (CommRingCat.of K))).X
  let a : T ⟶ G := (Gm.pointsEquiv (Spec (CommRingCat.of K)) T).symm (d.value x y)
  let p : T ⟶ E.X := x ≫ t
  let q : T ⟶ E.X := y ≫ t
  let eqv := d.pointEquiv T
  have hpq : p * q = ((x * y) ≫ t) * (a ≫ i.hom.hom) := by
    apply eqv.injective
    simp only [eqv, d.pointEquiv_mul, d.pointEquiv_apply]
    simp [p, q, t, i, a, d.inclusion_hom, comp_lift, SymmetricNormalized.pointMul, d.oneRight]
    have hs : (Gm.pointsEquiv _ T) ((Gm.pointsEquiv _ T).symm (d.value x y) ≫ 𝟙 G) =
        d.value x y := by rw [Category.comp_id, MulEquiv.apply_symm_apply]
    exact congrArg (fun s => (x * y, s)) hs.symm
  have hri : i.hom.hom ≫ r.hom.hom = 𝟙 G := congrArg (fun f => f.hom.hom) hr
  let χ (k : T ⟶ H.X) : Γ(T.left, ⊤)ˣ :=
    Gm.pointsEquiv (Spec (CommRingCat.of K)) T (k ≫ t ≫ r.hom.hom)
  have hχ (k : T ⟶ H.X) : Units.map k.left.appTop.hom.toMonoidHom b = (χ k)⁻¹ := by
    dsimp only [b, χ]
    rw [map_inv, ← Gm.pointsEquiv_naturality _ k (t ≫ r.hom.hom)]
  let eval : (T ⟶ (Gm (Spec (CommRingCat.of K))).X) ≃* Γ(T.left, ⊤)ˣ :=
    Gm.pointsEquiv _ T
  let w : T ⟶ E.X := (x * y) ≫ t
  have hm : χ x * χ y = χ (x * y) * d.value x y := by
    calc
      _ = eval ((p * q) ≫ r.hom.hom) := by
        rw [MonObj.mul_comp p q r.hom.hom, map_mul]
        simp only [p, q, χ, eval, Category.assoc]
      _ = eval ((w * (a ≫ i.hom.hom)) ≫ r.hom.hom) :=
        congrArg (fun v : T ⟶ E.X => eval (v ≫ r.hom.hom)) hpq
      _ = _ := by
        rw [MonObj.mul_comp w (a ≫ i.hom.hom) r.hom.hom, map_mul]
        simp only [w, χ, eval, Category.assoc, hri, Category.comp_id, a, MulEquiv.apply_symm_apply]
  rw [hχ (x * y), hχ x, hχ y, ← mul_inv, hm, mul_inv, mul_assoc, inv_mul_cancel, mul_one]

set_option maxHeartbeats 1000000 in
/-- A power that kills an affine commutative group scheme makes every scalar two-cocycle
into a coboundary after taking that power over an algebraically closed field. -/
theorem exists_correction_of_exponent (n : ℕ)
    (h : ∀ {T : Over (Spec (CommRingCat.of K))} (x : T ⟶ H.X), x ^ n = 1) : (c.power n).HasCorrection := by
  unfold HasCorrection
  let d := c.power n
  let e : SymmetricNormalized H :=
    ⟨d.normalized, d.normalized_one_left, d.normalized_one_right,
      fun x y => by
        change c.value x y ^ n / d.value 1 1 = c.value y x ^ n / d.value 1 1
        rw [c.pow_value_comm n h x y]⟩
  obtain ⟨b, hb⟩ := exists_correction_of_normalized e
  refine ⟨b / d.value (T := H.X) 1 1, ?_⟩
  intro T x y
  change _ = _ * d.value x y
  have hunit (x : T ⟶ H.X) :
      Units.map x.left.appTop.hom.toMonoidHom (d.value (T := H.X) 1 1) = d.value 1 1 := by
    rw [← d.precomp, MonObj.comp_one]
  simp only [map_div, hunit]
  rw [hb T]
  simp only [e, normalized]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

end Field

end UnitTwoCocycle

end Langlands.GroupScheme
