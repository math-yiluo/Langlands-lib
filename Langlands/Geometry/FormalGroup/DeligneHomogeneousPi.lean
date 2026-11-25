import Langlands.Geometry.FormalGroup.DeligneIsomorphism

/-! # Homogeneous iterates of the actual Deligne lattice operator -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory TopologicalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {X : TopCat.{u}}

/-- Actual multiplication by a coefficient on an O-module sheaf. -/
def moduleSheafScalar (a : O) (M : X.Sheaf (ModuleCat.{u} O)) : End M where
  asHom.hom := a • 𝟙 M.obj

/-- Every actual module-sheaf map commutes with coefficient multiplication. -/
theorem moduleSheafScalar_naturality (a : O) {M N : X.Sheaf (ModuleCat.{u} O)}
    (f : M ⟶ N) :
    (moduleSheafScalar a M).asHom ≫ f = f ≫ (moduleSheafScalar a N).asHom := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  exact (f.hom.app U).hom.map_smul a x

omit [NeZero d] in
/-- Powers of the actual sheaf operator evaluate as powers of its section map. -/
theorem latticePi_sheaf_pow_apply
    (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π)))
    (U : (Opens X)ᵒᵖ) (n : ℕ) (x : M.obj.obj U) :
    ((End.of (latticePi d π X M) ^ n).asHom.hom.app U) x =
      (((latticePi d π X M).hom.app U).hom ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change (latticePi d π X M).hom.app U
      (((End.of (latticePi d π X M) ^ n).asHom.hom.app U) x) = _
    rw [ih, pow_succ']
    rfl

omit [NeZero d] in
/-- The actual d-fold total sheaf map is multiplication by the integral scalar pi. -/
theorem latticePi_sheaf_relation
    (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) :
    End.of (latticePi d π X M) ^ d =
      moduleSheafScalar π (latticeScalarSheaf d π X M) := by
  apply End.ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  rw [latticePi_sheaf_pow_apply, latticePi_relation]
  rfl

namespace LatticePiSheaf

variable (M : LatticePiSheaf d π X)

omit [NeZero d] in
/-- Equality of degrees gives the actual component transport, compatible with inclusion. -/
theorem homogeneousTransport_inclusion {i j : ZMod d} (h : i = j) :
    eqToHom (congrArg M.component h) ≫ M.inclusion j = M.inclusion i := by
  subst j
  simp

/-- The n-fold homogeneous Pi map goes from degree i to degree i+n. -/
def piIterate (i : ZMod d) : (n : ℕ) → M.component i ⟶ M.component (i + (n : ZMod d))
  | 0 => eqToHom (congrArg M.component (by simp))
  | n + 1 => piIterate i n ≫ M.pi (i + (n : ZMod d)) ≫
      eqToHom (congrArg M.component (by simp [Nat.cast_add, add_assoc]))

omit [NeZero d] in
/-- Each homogeneous iterate is the restriction of the actual total Pi power. -/
@[reassoc]
theorem piIterate_inclusion (i : ZMod d) (n : ℕ) :
    M.piIterate i n ≫ M.inclusion (i + (n : ZMod d)) =
      M.inclusion i ≫ (End.of (latticePi d π X M.sheaf) ^ n).asHom := by
  induction n with
  | zero => simp [piIterate, M.homogeneousTransport_inclusion]
  | succ n ih =>
    dsimp only [piIterate]
    rw [Category.assoc, Category.assoc,
      M.homogeneousTransport_inclusion (by simp [Nat.cast_add, add_assoc]),
      M.pi_inclusion, ← Category.assoc, ih, Category.assoc]
    rw [pow_succ']
    rfl

/-- The homogeneous d-fold iterate closes to an endomorphism in its original degree. -/
def piCycle (i : ZMod d) : End (M.component i) :=
  End.of (M.piIterate i d ≫ eqToHom (congrArg M.component (by simp)))

omit [NeZero d] in
/-- A complete homogeneous cycle is the actual scalar pi on that component. -/
theorem piCycle_eq_scalar (i : ZMod d) :
    M.piCycle i = moduleSheafScalar π (M.component i) := by
  apply End.ext
  apply (cancel_mono (M.inclusion i)).mp
  dsimp only [piCycle]
  rw [Category.assoc,
    M.homogeneousTransport_inclusion (by simp),
    M.piIterate_inclusion, latticePi_sheaf_relation]
  exact (moduleSheafScalar_naturality π (M.inclusion i)).symm

/-- The complementary d-1 steps return from degree i+1 to degree i. -/
theorem piReturn_degree (i : ZMod d) : i + 1 + ((d - 1 : ℕ) : ZMod d) = i := by
  have hd : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hc : ((d - 1 : ℕ) : ZMod d) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] using
      congrArg (fun n : ℕ => (n : ZMod d)) hd
  calc
    i + 1 + ((d - 1 : ℕ) : ZMod d) = i + (((d - 1 : ℕ) : ZMod d) + 1) := by abel
    _ = i := by rw [hc, add_zero]

/-- The complementary d-1 steps give an actual return map from degree i+1 to i. -/
def piReturn (i : ZMod d) : M.component (i + 1) ⟶ M.component i :=
  M.piIterate (i + 1) (d - 1) ≫
    eqToHom (congrArg M.component (piReturn_degree i))

/-- The return map is the restriction of the complementary total Pi power. -/
@[reassoc]
theorem piReturn_inclusion (i : ZMod d) :
    M.piReturn i ≫ M.inclusion i =
      M.inclusion (i + 1) ≫ (End.of (latticePi d π X M.sheaf) ^ (d - 1)).asHom := by
  dsimp only [piReturn]
  rw [Category.assoc, M.homogeneousTransport_inclusion (piReturn_degree i),
    M.piIterate_inclusion]

/-- Forward Pi followed by the complementary path is scalar pi. -/
theorem pi_comp_return (i : ZMod d) :
    M.pi i ≫ M.piReturn i = (moduleSheafScalar π (M.component i)).asHom := by
  apply (cancel_mono (M.inclusion i)).mp
  rw [Category.assoc, M.piReturn_inclusion, ← Category.assoc, M.pi_inclusion,
    Category.assoc]
  have hd : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  change M.inclusion i ≫ (End.of (latticePi d π X M.sheaf) ^ (d - 1) *
    End.of (latticePi d π X M.sheaf)).asHom = _
  rw [← pow_succ, hd, latticePi_sheaf_relation]
  exact (moduleSheafScalar_naturality π (M.inclusion i)).symm

/-- The complementary path followed by forward Pi is scalar pi in the next degree. -/
theorem return_comp_pi (i : ZMod d) :
    M.piReturn i ≫ M.pi i = (moduleSheafScalar π (M.component (i + 1))).asHom := by
  apply (cancel_mono (M.inclusion (i + 1))).mp
  rw [Category.assoc, M.pi_inclusion, ← Category.assoc, M.piReturn_inclusion,
    Category.assoc]
  have hd : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  change M.inclusion (i + 1) ≫ (End.of (latticePi d π X M.sheaf) *
    End.of (latticePi d π X M.sheaf) ^ (d - 1)).asHom = _
  rw [← pow_succ', hd, latticePi_sheaf_relation]
  exact (moduleSheafScalar_naturality π (M.inclusion (i + 1))).symm

end LatticePiSheaf

open scoped ChangeOfRings

variable (F : Type u) [Field F] [Algebra O F]

/-- Rational scalar extension sends actual integral multiplication to the image scalar. -/
theorem rationalPresheaf_map_moduleSheafScalar
    (a : O) (M : X.Sheaf (ModuleCat.{u} O)) :
    (rationalPresheafFunctor F X).map (moduleSheafScalar a M).asHom =
      (algebraMap F (End ((rationalPresheafFunctor F X).obj M)) (algebraMap O F a)).asHom := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (1 : F) ⊗ₜ[O, algebraMap O F] (a • m) =
    algebraMap O F a • ((1 : F) ⊗ₜ[O, algebraMap O F] m)
  exact ((ModuleCat.extendRestrictScalarsAdj (algebraMap O F)).unit.app
    (M.obj.obj U)).hom.map_smul a m

namespace LatticePiSheaf

variable (M : LatticePiSheaf d π X) (hπ : algebraMap O F π ≠ 0)

/-- The actual rational component Pi map is already invertible before sheafification. -/
def rationalPiPresheafIso (i : ZMod d) :
    (rationalPresheafFunctor F X).obj (M.component i) ≅
      (rationalPresheafFunctor F X).obj (M.component (i + 1)) where
  hom := (rationalPresheafFunctor F X).map (M.pi i)
  inv := (algebraMap O F π)⁻¹ • (rationalPresheafFunctor F X).map (M.piReturn i)
  hom_inv_id := by
    rw [Linear.comp_smul, ← Functor.map_comp, M.pi_comp_return,
      rationalPresheaf_map_moduleSheafScalar]
    rw [Algebra.algebraMap_eq_smul_one (R := F), End.smul_asHom, smul_smul, inv_mul_cancel₀ hπ,
      one_smul]
    rfl
  inv_hom_id := by
    rw [Linear.smul_comp, ← Functor.map_comp, M.return_comp_pi,
      rationalPresheaf_map_moduleSheafScalar]
    rw [Algebra.algebraMap_eq_smul_one (R := F), End.smul_asHom, smul_smul, inv_mul_cancel₀ hπ,
      one_smul]
    rfl

/-- Actual sheafification gives the rational isomorphism from degree i to degree i+1. -/
def rationalPiIso (i : ZMod d) :
    M.rationalComponent F i ≅ M.rationalComponent F (i + 1) :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).mapIso
    (M.rationalPiPresheafIso F hπ i)

/-- The constructed forward isomorphism is exactly rationalization of the integral Pi map. -/
theorem rationalPiIso_hom (i : ZMod d) :
    (M.rationalPiIso F hπ i).hom = (rationalSheafFunctor F X).map (M.pi i) := rfl

/-- Every nonnegative homogeneous Pi iterate is a constructed rational isomorphism. -/
def rationalPiIterateIso (i : ZMod d) :
    (n : ℕ) → M.rationalComponent F i ≅ M.rationalComponent F (i + (n : ZMod d))
  | 0 => (rationalSheafFunctor F X).mapIso
      (eqToIso (congrArg M.component (by simp)))
  | n + 1 => rationalPiIterateIso i n ≪≫
      M.rationalPiIso F hπ (i + (n : ZMod d)) ≪≫
        (rationalSheafFunctor F X).mapIso
          (eqToIso (congrArg M.component (by simp [Nat.cast_add, add_assoc])))

/-- The forward map of the rational iterate is precisely the actual integral iterate's image. -/
theorem rationalPiIterateIso_hom (i : ZMod d) (n : ℕ) :
    (M.rationalPiIterateIso F hπ i n).hom =
      (rationalSheafFunctor F X).map (M.piIterate i n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [rationalPiIterateIso, Iso.trans_hom]
    rw [ih, M.rationalPiIso_hom F hπ]
    simp only [piIterate, Functor.map_comp, Functor.mapIso_hom]
    rfl

/-- Taking an actual rational homogeneous component is functorial. -/
def rationalComponentFunctor (i : ZMod d) :
    LatticePiSheaf d π X ⥤ X.Sheaf (ModuleCat.{u} F) :=
  componentFunctor i ⋙ rationalSheafFunctor F X

/-- The rational degree-one isomorphisms are natural in genuine homogeneous lattice maps. -/
def rationalPiNatIso (i : ZMod d) :
    rationalComponentFunctor (π := π) (X := X) F i ≅
      rationalComponentFunctor F (i + 1) :=
  NatIso.ofComponents (fun M => M.rationalPiIso F hπ i) (fun {M N} f => by
    change (rationalSheafFunctor F X).map (f.component i) ≫
        (rationalSheafFunctor F X).map (N.pi i) =
      (rationalSheafFunctor F X).map (M.pi i) ≫
        (rationalSheafFunctor F X).map (f.component (i + 1))
    rw [← Functor.map_comp, ← Functor.map_comp, f.pi_naturality])

end LatticePiSheaf

end Langlands.DeligneFormalSpace
