/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.PrimaryModuleFiltrationFixedFieldComparison
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension
import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.Algebra.Field.ULift

/-!
# Constant prime-field quotient identification

Source: Stacks Project, Tag 04JQ; blueprint `theorem-cohomology-curves--2`,
proof paragraphs 1--2.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits ZeroObject Opposite
namespace AlgebraicGeometry.Scheme

private theorem finite_prime_group_coordinates (G : Type (u + 1)) [AddCommGroup G]
    [Finite G] (ℓ : ℕ) (hℓ : ℓ.Prime) (hkill : ∀ x : G, ℓ • x = 0) :
    ∃ d : ℕ, Nonempty (G ≃+ (Fin d → ULift.{u + 1} (ZMod ℓ))) := by
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let : Module (ZMod ℓ) G := AddCommGroup.zmodModule hkill
  let F := ULift.{u + 1} (ZMod ℓ)
  let : Module F G := Module.compHom G ULift.ringEquiv.toRingHom
  let I := Module.Basis.ofVectorSpaceIndex F G
  let b : Module.Basis I F G := Module.Basis.ofVectorSpace F G
  have : Finite I := Finite.of_injective b b.injective
  let : Fintype I := Fintype.ofFinite I
  let c := b.reindex (Fintype.equivFin I)
  exact ⟨Fintype.card I, ⟨c.equivFun.toAddEquiv⟩⟩

private theorem constant_fin_power (T : Scheme.{u}) (ℓ d : ℕ) :
    Nonempty ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (Fin d → ULift.{u + 1} (ZMod ℓ))) ≅
        Nat.rec (0 : _) (fun _ V ↦ V ⊞ T.constantZMod ℓ) d) := by
  let F := constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}
  let : F.Additive := inferInstanceAs
    (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  induction d with
  | zero =>
    exact ⟨(F.map_isZero (AddCommGrpCat.isZero_of_subsingleton _)).isoZero⟩
  | succ d hd =>
    obtain ⟨hd⟩ := hd
    let a : (Fin (d + 1) → ULift.{u + 1} (ZMod ℓ)) ≃+
        ((Fin d → ULift.{u + 1} (ZMod ℓ)) × ULift.{u + 1} (ZMod ℓ)) :=
      { toEquiv := (Fin.snocEquiv (fun _ ↦ ULift.{u + 1} (ZMod ℓ))).symm.trans
          (Equiv.prodComm _ _)
        map_add' := by intros; rfl }
    exact ⟨F.mapIso (a.toAddCommGrpIso ≪≫ (AddCommGrpCat.biprodIsoProd _ _).symm) ≪≫
      F.mapBiprod (AddCommGrpCat.of (Fin d → ULift.{u + 1} (ZMod ℓ)))
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) ≪≫ biprod.mapIso hd (Iso.refl _)⟩

/-- Source: Stacks Project, Tags 04JQ, 03QT and 03QW; blueprint
`theorem-cohomology-curves--2`, proof paragraphs 1--2.
(blueprint: lem-sc-primary-constant-quotient-identification)

Proof: Set L = Ks^H. The canonical map from V to the geometric stalk of
its constant sheaf on Spec L is an additive isomorphism. Given g in H,
extend g to a K-automorphism tau of Omega. It fixes L: for a in L the
extension identity gives tau(a) = g(a) = a. Consequently Spec(tau) followed
by the geometric point t is t. Apply the stipulated action formula to the
identity etale neighbourhood, the identical lifts x = x', and the global
constant section associated to v in V. It says that the action fixes the
constant germ of v.
The canonical stalk map is surjective, so this action is trivial on all
stalk elements. Composing the stalk map with C's inverse fiber isomorphism
gives an equivariant additive, hence integer-linear, isomorphism between
the trivial representation V and C applied to its constant sheaf. Full
faithfulness and C's unit identify C.inverse of that representation with
the constant sheaf on Spec L. Pullback across e.inv preserves constant
sheaves by the constant-sheaf adjunction, yielding the displayed isomorphism.
The argument applies also to the zero group and needs neither finiteness
nor a prime nor a subgroup quotient. -/
private theorem primary_trivialRepresentation_constant
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (H : OpenSubgroup (Gal(Ks/K))) (C : PrimaryFixedFieldEquivalence K Ks H)
    (hC : PrimaryFixedFieldComparison K Ks H Ω C)
    (T : Scheme.{u}) (e : Spec (.of (IntermediateField.fixedField H.toSubgroup)) ≅ T)
    (V : Type (u + 1)) [AddCommGroup V] :
    Nonempty (primaryAssociatedSheaf K Ks H Ω C T e
      ⟨Rep.trivial ℤ H.toSubgroup V, fun _ ↦ by simp⟩ ≅
        (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of V)) := by
  classical
  let L := IntermediateField.fixedField H.toSubgroup
  let S := Spec (.of L)
  let t : Spec (.of Ω) ⟶ S := Spec.map (CommRingCat.ofHom
    ((algebraMap Ks Ω).comp (algebraMap L Ks)))
  let P := primaryFixedFieldPoint K Ks H Ω
  let F := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of V)
  obtain ⟨j, hj⟩ := hC
  let U : S.Etale := Etale.mk (𝟙 S)
  let x : P.fiber.obj U := Over.homMk t (Category.comp_id t)
  let a : AddCommGrpCat.of V ⟶ P.sheafFiber.obj F :=
    (toSheafify S.smallEtaleTopology
      ((Functor.const S.Etaleᵒᵖ).obj (AddCommGrpCat.of V))).app (op U) ≫
        P.toPresheafFiber U x F.obj
  have : IsIso a := constantSheaf_geometricStalk_isIso S (AddCommGrpCat.of V) t
  let b : AddCommGrpCat.of V ≅ (primaryModuleForget K Ks H).obj (C.functor.obj F) :=
    asIso a ≪≫ (j.app F).symm
  have hb (g : H.toSubgroup) (v : V) :
      (C.functor.obj F).obj.ρ g (b.hom v) = b.hom v := by
    obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K Ks Ω g.val
    have ht : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ t = t := by
      change Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ((algebraMap Ks Ω).comp (algebraMap L Ks))) = _
      rw [← Spec.map_comp]
      congr 1
      ext y
      have hy := congrArg (fun f : Ks →+* Ω ↦ f (y : Ks)) hτ
      have hg : g.val (y : Ks) = (y : Ks) := by
        have hy' : (y : Ks) ∈ IntermediateField.fixedField H.toSubgroup := y.property
        rw [IntermediateField.mem_fixedField_iff] at hy'
        exact hy' g.val g.property
      change τ (algebraMap Ks Ω (y : Ks)) = algebraMap Ks Ω (y : Ks)
      change algebraMap Ks Ω (g.val (y : Ks)) = τ (algebraMap Ks Ω (y : Ks)) at hy
      rw [hg] at hy
      exact hy.symm
    have hx : x.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left := ht.symm
    have h := hj F g τ hτ U x x hx
      ((toSheafify S.smallEtaleTopology
        ((Functor.const S.Etaleᵒᵖ).obj (AddCommGrpCat.of V))).app (op U) v)
    change (j.hom.app F) ((C.functor.obj F).obj.ρ g (b.hom v)) = a v at h
    have h' := congrArg (fun y ↦ (j.inv.app F) y) h
    have hc (y : (C.functor.obj F).obj.V) :
        (j.inv.app F) ((j.hom.app F) y) = y := by
      have z := congrArg (fun f ↦ f y) (Iso.hom_inv_id_app j F)
      simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using z
    calc
      (C.functor.obj F).obj.ρ g (b.hom v) =
          (j.inv.app F) ((j.hom.app F) ((C.functor.obj F).obj.ρ g (b.hom v))) :=
        (hc _).symm
      _ = (j.inv.app F) (a v) := h'
      _ = b.hom v := rfl
  let b' : V ≃+ (C.functor.obj F).obj.V :=
    { toFun := b.hom
      invFun := b.inv
      left_inv := fun v ↦ by simp
      right_inv := fun v ↦ by simp
      map_add' := fun v w ↦ map_add b.hom.hom v w }
  let : Module ℤ (C.functor.obj F).obj.V := (C.functor.obj F).obj.hV2
  let bL : V ≃ₗ[ℤ] (C.functor.obj F).obj.V :=
    b'.toIntLinearEquiv (modM₂ := (C.functor.obj F).obj.hV2)
  let rE : (Rep.trivial ℤ H.toSubgroup V).ρ.Equiv (C.functor.obj F).obj.ρ :=
    { toLinearEquiv := bL
      isIntertwining' := fun g ↦ by
        ext v
        exact (hb g v).symm }
  let r : (Rep.trivial ℤ H.toSubgroup V) ≅ (C.functor.obj F).obj := Rep.mkIso rE
  let r' : (⟨Rep.trivial ℤ H.toSubgroup V, fun _ ↦ by simp⟩ :
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ H.toSubgroup) ≅ C.functor.obj F :=
    ObjectProperty.isoMk _ r
  exact ⟨(Etale.upperStar AddCommGrpCat.{u + 1} e.inv).mapIso
    (C.inverse.mapIso r' ≪≫ (C.unitIso.app F).symm) ≪≫
      (upperStarConstantSheafIso AddCommGrpCat.{u + 1} e.inv).app (AddCommGrpCat.of V)⟩

/-- Source: Stacks Project, Tag 04JQ; blueprint `theorem-cohomology-curves--2`,
proof paragraphs 1--2.
(blueprint: lem-sc-primary-constant-quotient-identification)

Proof: Let Q be the explicitly constructed additive quotient B/(A ∩ B). Its elements are
represented by x in B. The condition ell*x in A implies ell*q=0 for every q in Q.
An abelian group annihilated by ell has the canonical ZMod ell module structure,
induced by integer multiplication modulo ell. Because ell is prime this ring is a
field. Q is finite as a quotient of a subgroup of the finite ambient module, hence
finite-dimensional over this field. Choose a finite basis of cardinal d. Its coordinate
map identifies Q with d copies of ZMod ell, additively and equivariantly since the
specified action on both sides is trivial. Under C, a constant sheaf has its value as
geometric stalk and trivial monodromy: constant germs stay constant when the pointed
lift changes. Conversely the canonical stalk/action comparison and full faithfulness
identify the associated sheaf of a trivial representation with that constant sheaf.
Preservation of finite products and coproducts transports the coordinate isomorphism
to finite biproducts, with the zero-dimensional case giving the zero sheaf. Pullback
across e preserves constant sheaves and binary biproducts; induction on d identifies
this biproduct with the displayed Nat.rec expression. When A=B or B=0, d=0 works.
There is no terminal sheaf or chain in this assertion. -/
theorem primaryTrivialQuotient_constant
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (H : OpenSubgroup (Gal(Ks/K))) (C : PrimaryFixedFieldEquivalence K Ks H)
    (hC : PrimaryFixedFieldComparison K Ks H Ω C)
    (T : Scheme.{u}) (e : Spec (.of (IntermediateField.fixedField H.toSubgroup)) ≅ T)
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K))) [Finite R.obj.V]
    (A B : AddSubgroup R.obj.V) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hkill : ∀ x : R.obj.V, x ∈ B → ℓ • x ∈ A) :
    ∃ d : ℕ, Nonempty
      (primaryAssociatedSheaf K Ks H Ω C T e (primaryTrivialQuotient K Ks H R A B) ≅
        Nat.rec (0 : _) (fun _ V ↦ V ⊞ T.constantZMod ℓ) d) := by
  let Q := B.toIntSubmodule ⧸ primaryRelativeSubmodule K Ks R A B
  have : Finite B.toIntSubmodule := Finite.of_injective
    ((↑) : B.toIntSubmodule → R.obj.V) Subtype.val_injective
  have : Finite Q := Finite.of_surjective
    (Submodule.Quotient.mk : B.toIntSubmodule → Q)
    (Submodule.Quotient.mk_surjective _)
  have hQ : ∀ x : Q, ℓ • x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hkill x x.property
  obtain ⟨d, ⟨a⟩⟩ := finite_prime_group_coordinates Q ℓ hℓ hQ
  obtain ⟨j⟩ := primary_trivialRepresentation_constant K Ks Ω H C hC T e Q
  obtain ⟨b⟩ := constant_fin_power T ℓ d
  exact ⟨d, ⟨j ≪≫ (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
    a.toAddCommGrpIso ≪≫ b⟩⟩

end AlgebraicGeometry.Scheme
