/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
import Mathlib.Algebra.DirectSum.Algebra

/-! # Total algebra of a graded sheaf algebra

Source: Stacks Project, Modules, Section 01CF; Modules on Sites, Tag 03DB.
(blueprint: lem-trf-graded-sheaf-algebra-total).
-/

@[expose] public section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

namespace AlgebraicGeometry.GradedSheafAlgebra

private class Input {X : Scheme.{u}} (P : ℕ → X.Modules) where
  graded : GradedSheafAlgebra P
noncomputable section
variable {X : Scheme.{u}} {P : ℕ → X.Modules}

private abbrev Piece [Input P] (U : X.Opensᵒᵖ) (n : ℕ) : Type u := (P n).val.obj U

private instance gradedMul [Input P] (U : X.Opensᵒᵖ) : GradedMonoid.GMul (Piece (P := P) U) :=
  ⟨fun {m n} a b ↦ (Input.graded (P := P)).mul m n U.unop a b⟩

private instance gradedOne [Input P] (U : X.Opensᵒᵖ) : GradedMonoid.GOne (Piece (P := P) U) :=
  ⟨(Input.graded (P := P)).unit.val.app U (1 : X.presheaf.obj U)⟩

private instance gradedRing [Input P] (U : X.Opensᵒᵖ) : DirectSum.GCommRing (Piece (P := P) U) where
  mul := fun {m n} ↦ fun a b ↦ (Input.graded (P := P)).mul m n U.unop a b
  one := (Input.graded (P := P)).unit.val.app U (1 : X.presheaf.obj U)
  mul_zero a := ((Input.graded (P := P)).mul _ _ U.unop a).map_zero
  zero_mul {i j} b := by
    exact LinearMap.congr_fun ((Input.graded (P := P)).mul i j U.unop).map_zero b
  mul_add a b c := ((Input.graded (P := P)).mul _ _ U.unop a).map_add b c
  add_mul a b c := by
    exact congrArg (fun f ↦ f c) (((Input.graded (P := P)).mul _ _ U.unop).map_add a b)
  one_mul := fun ⟨n, a⟩ ↦ Sigma.ext (Nat.zero_add n) ((Input.graded (P := P)).one_mul n U.unop a)
  mul_one := fun ⟨n, a⟩ ↦ Sigma.ext (Nat.add_zero n) ((Input.graded (P := P)).mul_one n U.unop a)
  mul_assoc := fun ⟨l, a⟩ ⟨m, b⟩ ⟨n, c⟩ ↦
    Sigma.ext (Nat.add_assoc l m n) ((Input.graded (P := P)).assoc l m n U.unop a b c)
  mul_comm := fun ⟨m, a⟩ ⟨n, b⟩ ↦
    Sigma.ext (Nat.add_comm m n) ((Input.graded (P := P)).comm m n U.unop a b)
  natCast n := (Input.graded (P := P)).unit.val.app U (n : X.presheaf.obj U)
  natCast_zero := by simp
  natCast_succ n := by simp [Nat.cast_add, Nat.cast_one]
  intCast n := (Input.graded (P := P)).unit.val.app U (n : X.presheaf.obj U)
  intCast_ofNat n := by simp
  intCast_negSucc_ofNat n := by simp

private instance gradedAlgebra [Input P] (U : X.Opensᵒᵖ) :
    DirectSum.GAlgebra (X.presheaf.obj U) (Piece (P := P) U) where
  toFun := ((Input.graded (P := P)).unit.val.app U).hom.toAddMonoidHom
  map_one := rfl
  map_mul r s := by
    apply congrArg (GradedMonoid.mk 0)
    change (Input.graded (P := P)).unit.val.app U (r * s) =
      (Input.graded (P := P)).mul 0 0 U.unop ((Input.graded (P := P)).unit.val.app U r)
        ((Input.graded (P := P)).unit.val.app U s)
    have hu (r : X.presheaf.obj U) :
        (Input.graded (P := P)).unit.val.app U r =
          r • (Input.graded (P := P)).unit.val.app U (1 : X.presheaf.obj U) := by
      simpa using ((Input.graded (P := P)).unit.val.app U).hom.map_smul r (1 : X.presheaf.obj U)
    rw [hu r, ((Input.graded (P := P)).mul 0 0 U.unop).map_smul]
    change (Input.graded (P := P)).unit.val.app U (r * s) = r •
      (Input.graded (P := P)).mul 0 0 U.unop
        ((Input.graded (P := P)).unit.val.app U (1 : X.presheaf.obj U))
        ((Input.graded (P := P)).unit.val.app U s)
    rw [eq_of_heq ((Input.graded (P := P)).one_mul 0 U.unop _)]
    exact ((Input.graded (P := P)).unit.val.app U).hom.map_smul r s
  commutes r := fun ⟨n, a⟩ ↦
    Sigma.ext ((Nat.zero_add n).trans (Nat.add_zero n).symm)
      ((Input.graded (P := P)).comm 0 n U.unop _ a)
  smul_def r := fun ⟨n, a⟩ ↦ by
    apply Sigma.ext (Nat.zero_add n).symm
    have hu : (Input.graded (P := P)).unit.val.app U r = r • (Input.graded (P := P)).unit.val.app U
        (1 : X.presheaf.obj U) := by
      simpa using ((Input.graded (P := P)).unit.val.app U).hom.map_smul r (1 : X.presheaf.obj U)
    change HEq (r • a)
      ((Input.graded (P := P)).mul 0 n U.unop ((Input.graded (P := P)).unit.val.app U r) a)
    rw [hu, (Input.graded (P := P)).mul 0 n U.unop |>.map_smul]
    change HEq (r • a)
      (r • (Input.graded (P := P)).mul 0 n U.unop
        ((Input.graded (P := P)).unit.val.app U (1 : X.presheaf.obj U)) a)
    have aux {i j : ℕ} (h : i = j) (x : Piece (P := P) U i)
        (y : Piece (P := P) U j) (hxy : HEq x y) : HEq (r • x) (r • y) := by
      subst j
      cases hxy
      rfl
    exact (aux (Nat.zero_add n) _ _ ((Input.graded (P := P)).one_mul n U.unop a)).symm

private abbrev Sum [Input P] (U : X.Opensᵒᵖ) := ⨁ n : ℕ, Piece (P := P) U n

private def restriction [Input P] {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    Sum (P := P) U →+* Sum (P := P) V :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (Piece (P := P) V) n).comp
      ((P n).val.map f).hom.toAddMonoidHom)
    (by
      change DirectSum.of (Piece (P := P) V) 0
        ((P 0).val.map f ((Input.graded (P := P)).unit.val.app U
          (1 : X.presheaf.obj U))) =
        DirectSum.of (Piece (P := P) V) 0
          ((Input.graded (P := P)).unit.val.app V (1 : X.presheaf.obj V))
      congr 1
      have h := PresheafOfModules.naturality_apply (Input.graded (P := P)).unit.val f
        (1 : X.presheaf.obj U)
      change (Input.graded (P := P)).unit.val.app V (X.presheaf.map f 1) = _ at h
      simpa only [map_one] using h.symm)
    (by
      intro m n a b
      change DirectSum.of (Piece (P := P) V) (m + n)
        ((P (m + n)).val.map f ((Input.graded (P := P)).mul m n U.unop a b)) =
        DirectSum.of (Piece (P := P) V) m ((P m).val.map f a) *
          DirectSum.of (Piece (P := P) V) n ((P n).val.map f b)
      rw [DirectSum.of_mul_of]
      congr 1
      exact (Input.graded (P := P)).naturality m n U.unop V.unop f.unop.le a b)

private theorem restriction_of [Input P] {U V : X.Opensᵒᵖ} (f : U ⟶ V) (n : ℕ)
    (a : Piece (P := P) U n) :
    restriction f (DirectSum.of _ n a) = DirectSum.of (Piece (P := P) V) n ((P n).val.map f a) := by
  exact DirectSum.toSemiring_of _ _ _ _ _

private noncomputable def ringPresheaf [Input P] : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (Sum (P := P) U)
  map f := CommRingCat.ofHom (restriction f)
  map_id U := by
    apply CommRingCat.hom_ext
    apply DirectSum.ringHom_ext
    intro n a
    change restriction (𝟙 U) (DirectSum.of _ n a) = DirectSum.of _ n a
    rw [restriction_of]
    congr 1
    simp
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply DirectSum.ringHom_ext
    intro n a
    change restriction (f ≫ g) (DirectSum.of _ n a) =
      restriction g (restriction f (DirectSum.of _ n a))
    rw [restriction_of, restriction_of, restriction_of]
    congr 1
    exact (P n).val.map_comp_apply f g a

private theorem restriction_algebraMap [Input P] {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (r : X.presheaf.obj U) :
    restriction f (algebraMap (X.presheaf.obj U) (Sum (P := P) U) r) =
      algebraMap (X.presheaf.obj V) (Sum (P := P) V) (X.presheaf.map f r) := by
  rw [DirectSum.algebraMap_apply, DirectSum.algebraMap_apply, restriction_of]
  congr 1
  exact (PresheafOfModules.naturality_apply (Input.graded (P := P)).unit.val f r).symm

private noncomputable def structureMap [Input P] : X.presheaf ⟶ ringPresheaf (P := P) where
  app U := CommRingCat.ofHom (algebraMap _ _)
  naturality {U V} f := by
    ext r
    exact (restriction_algebraMap f r).symm

private noncomputable def algebra [Input P] : X.CommAlgebraSheaf :=
  Under.mk (show X.sheaf ⟶
    (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj
      (ringPresheaf (P := P)) from
        ⟨structureMap (P := P) ≫ toSheafify _ (ringPresheaf (P := P))⟩)

private noncomputable def sumRestriction [Input P] {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    ModuleCat.of (X.presheaf.obj U) (Sum (P := P) U) ⟶
      (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
        (ModuleCat.of (X.presheaf.obj V) (Sum (P := P) V)) :=
  let N := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
    (ModuleCat.of (X.presheaf.obj V) (Sum (P := P) V))
  ModuleCat.ofHom (Y := N) (DirectSum.toModule _ ℕ N fun n ↦
    { toFun := fun a ↦ DirectSum.of (Piece (P := P) V) n ((P n).val.map f a)
      map_add' := by intro a b; simp
      map_smul' := by
        intro r a
        change DirectSum.of (Piece (P := P) V) n ((P n).val.map f (r • a)) =
          X.presheaf.map f r • DirectSum.of (Piece (P := P) V) n ((P n).val.map f a)
        rw [(P n).val.map_smul, DirectSum.of_smul]
        rfl })

private theorem sumRestriction_of [Input P] {U V : X.Opensᵒᵖ} (f : U ⟶ V) (n : ℕ)
    (a : Piece (P := P) U n) :
    sumRestriction f (DirectSum.of _ n a) =
      DirectSum.of (Piece (P := P) V) n ((P n).val.map f a) := by
  exact DirectSum.toModule_lof _ _ _

private noncomputable def modulePresheaf [Input P] : PresheafOfModules X.ringCatSheaf.obj where
  obj U := ModuleCat.of (X.presheaf.obj U) (Sum (P := P) U)
  map f := sumRestriction f
  map_id U := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro n
    ext a
    change sumRestriction (𝟙 U) (DirectSum.of _ n a) = DirectSum.of _ n a
    rw [sumRestriction_of]
    congr 1
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro n
    ext a
    change sumRestriction (f ≫ g) (DirectSum.of _ n a) =
      sumRestriction g (sumRestriction f (DirectSum.of _ n a))
    rw [sumRestriction_of, sumRestriction_of, sumRestriction_of]
    congr 1
    exact (P n).val.map_comp_apply f g a

private noncomputable def presheafInclusion [Input P] (n : ℕ) : (P n).val ⟶
    modulePresheaf (P := P) where
  app U := ModuleCat.ofHom (DirectSum.lof _ ℕ (Piece (P := P) U) n)
  naturality {U V} f := by
    ext a
    exact (sumRestriction_of f n a).symm

private noncomputable def presheafCofanIsColimit [Input P] :
    IsColimit (Cofan.mk (modulePresheaf (P := P)) (presheafInclusion (P := P))) := by
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro U
  refine IsColimit.mk (fun s ↦ ModuleCat.ofHom
    (DirectSum.toModule _ ℕ s.pt (fun n ↦ (s.ι.app ⟨n⟩).hom))) ?_ ?_
  · intro s j
    apply ModuleCat.hom_ext
    ext a
    change (DirectSum.toModule (X.presheaf.obj U) ℕ s.pt
      (fun n ↦ (s.ι.app ⟨n⟩).hom)) (DirectSum.of (Piece (P := P) U) j.as a) = _
    exact DirectSum.toModule_lof _ _ _
  · intro s m hm
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro a
    have hh := ConcreteCategory.congr_hom (hm ⟨n⟩) a
    change m (DirectSum.of _ n a) = _ at hh
    change m (DirectSum.of (Piece (P := P) U) n a) =
      (DirectSum.toModule (X.presheaf.obj U) ℕ s.pt
        (fun n ↦ (s.ι.app ⟨n⟩).hom)) (DirectSum.of (Piece (P := P) U) n a)
    exact hh.trans (DirectSum.toModule_lof (X.presheaf.obj U)
      (M := Piece (P := P) U) (N := s.pt)
      (φ := fun k : ℕ ↦ (s.ι.app ⟨k⟩).hom) n a).symm

private theorem restriction_eq_sumRestriction [Input P] {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (s : Sum (P := P) U) : restriction f s = sumRestriction f s := by
  induction s using DirectSum.induction_on with
  | zero => simp
  | of n a => rw [restriction_of, sumRestriction_of]
  | add a b ha hb => simp only [map_add, ha, hb]

private noncomputable def toTotal [Input P] :
    modulePresheaf (P := P) ⟶ (algebra (P := P)).toModule.val where
  app U := ModuleCat.ofHom (Y := (algebra (P := P)).toModule.val.obj U)
    { toFun := (toSheafify (Opens.grothendieckTopology X)
        (ringPresheaf (P := P))).app U
      map_add' := map_add _
      map_smul' := by
        intro r a
        let η := toSheafify (Opens.grothendieckTopology X) (ringPresheaf (P := P))
        change η.app U (r • a) = η.app U (algebraMap _ (Sum (P := P) U) r) * η.app U a
        rw [Algebra.smul_def, map_mul] }
  naturality {U V} f := by
    ext s
    change (toSheafify _ (ringPresheaf (P := P))).app V (sumRestriction f s) =
      (algebra (P := P)).right.obj.map f ((toSheafify _ (ringPresheaf (P := P))).app U s)
    rw [← restriction_eq_sumRestriction f s]
    exact NatTrans.naturality_apply
      (toSheafify (Opens.grothendieckTopology X) (ringPresheaf (P := P))) f s

private theorem toTotal_locallyBijective [Input P] :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (toTotal (P := P)) ∧
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (toTotal (P := P)) := by
  let J := Opens.grothendieckTopology X
  let η := toSheafify J (ringPresheaf (P := P))
  have hi := (J.W_toSheafify (ringPresheaf (P := P))).isLocallyInjective
  have hs := (J.W_toSheafify (ringPresheaf (P := P))).isLocallySurjective
  constructor
  · constructor
    intro U x y hxy
    have h := hi.equalizerSieve_mem x y hxy
    convert h using 1
    ext V f
    change sumRestriction f.op x = sumRestriction f.op y ↔
      restriction f.op x = restriction f.op y
    rw [restriction_eq_sumRestriction, restriction_eq_sumRestriction]
  · constructor
    intro U s
    exact hs.imageSieve_mem s

private noncomputable def inclusion [Input P] (n : ℕ) : P n ⟶ (algebra (P := P)).toModule :=
  ⟨presheafInclusion n ≫ toTotal (P := P)⟩

private noncomputable def coproduct [Input P] :
    IsColimit (Cofan.mk (algebra (P := P)).toModule (inclusion (P := P))) := by
  letI hi := (toTotal_locallyBijective (P := P)).1
  letI hs := (toTotal_locallyBijective (P := P)).2
  let h := presheafCofanIsColimit (P := P)
  let e (N : X.Modules) := PresheafOfModules.homEquivOfIsLocallyBijective
    (f := toTotal (P := P)) N.isSheaf
  refine Cofan.IsColimit.mk _ ?_ ?_ ?_
  · intro s
    exact ⟨(e s.pt).symm (Cofan.IsColimit.desc h (fun n ↦ (s.inj n).val))⟩
  · intro s n
    apply SheafOfModules.hom_ext
    change (presheafInclusion n ≫ toTotal (P := P)) ≫
      (e s.pt).symm (Cofan.IsColimit.desc h (fun n ↦ (s.inj n).val)) = _
    rw [Category.assoc]
    change presheafInclusion n ≫
      (e s.pt) ((e s.pt).symm (Cofan.IsColimit.desc h (fun n ↦ (s.inj n).val))) = _
    rw [(e s.pt).apply_symm_apply]
    exact Cofan.IsColimit.fac h (fun n ↦ (s.inj n).val) n
  · intro s m hm
    apply SheafOfModules.hom_ext
    apply (e s.pt).injective
    rw [(e s.pt).apply_symm_apply]
    apply Cofan.IsColimit.hom_ext h
    intro n
    exact (congrArg SheafOfModules.Hom.val (hm n)).trans
      (Cofan.IsColimit.fac h (fun n ↦ (s.inj n).val) n).symm

end

/-- A graded sheaf algebra has a total commutative algebra sheaf whose underlying
module is the coproduct of its pieces. The inclusions respect multiplication and scalars.
Source: Stacks Project, Modules, Section 01CF; Modules on Sites, Tag 03DB
(blueprint: lem-trf-graded-sheaf-algebra-total).

Proof: Give the sectionwise direct sum its graded ring structure, using the specified
bilinear products and the degree-zero unit. Restrictions preserve these operations.
Sheafify this presheaf of commutative rings and compose its structure morphism with
the sheafification unit. The resulting unit map from the direct-sum module presheaf is
locally bijective: its underlying sections and restriction functions are those of ring
sheafification. Maps from this presheaf into a module sheaf therefore extend uniquely.
Together with the sectionwise direct-sum universal property, this proves the coproduct
universal property. The two displayed formulas follow by applying the ring
sheafification map to homogeneous multiplication and the degree-zero algebra map. -/
theorem exists_total {X : Scheme.{u}} (P : ℕ → X.Modules)
    (G : GradedSheafAlgebra P) :
    ∃ (B : X.CommAlgebraSheaf) (i : ∀ n, P n ⟶ B.toModule),
      Nonempty (IsColimit (Cofan.mk B.toModule i)) ∧
      (∀ (U : X.Opens) (m n : ℕ) (a : (P m).val.obj (op U))
        (b : (P n).val.obj (op U)),
        (i (m + n)).val.app (op U) (G.mul m n U a b) =
          (@id (B.right.obj.obj (op U)) ((i m).val.app (op U) a)) *
            (@id (B.right.obj.obj (op U)) ((i n).val.app (op U) b))) ∧
      (∀ (U : X.Opens) (r : Γ(X, U)),
        (i 0).val.app (op U) (G.unit.val.app (op U) r) = B.hom.hom.app (op U) r) := by
  let : Input P := ⟨G⟩
  refine ⟨algebra, inclusion, ⟨coproduct⟩, ?_, ?_⟩
  · intro U m n a b
    change (toSheafify _ (ringPresheaf (P := P))).app (op U)
      (DirectSum.of (Piece (P := P) (op U)) (m + n) (G.mul m n U a b)) =
      (toSheafify _ (ringPresheaf (P := P))).app (op U)
        (DirectSum.of (Piece (P := P) (op U)) m a) *
      (toSheafify _ (ringPresheaf (P := P))).app (op U)
        (DirectSum.of (Piece (P := P) (op U)) n b)
    rw [← map_mul, DirectSum.of_mul_of]
    rfl
  · intro U r
    change (toSheafify _ (ringPresheaf (P := P))).app (op U)
      (DirectSum.of (Piece (P := P) (op U)) 0 (G.unit.val.app (op U) r)) =
      (toSheafify _ (ringPresheaf (P := P))).app (op U)
        (algebraMap _ (Sum (P := P) (op U)) r)
    rfl

end AlgebraicGeometry.GradedSheafAlgebra
end
