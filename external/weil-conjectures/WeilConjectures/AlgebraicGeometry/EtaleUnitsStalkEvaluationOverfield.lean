/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.EtaleUnitsStalkEvaluationOverfieldBijective

/-!
# Evaluation of geometric units germs in a separable closure

Source: Stacks Project, Tag 03QV, Example sheaves-point (2), and Tag 02GL.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

private theorem evaluation_isSeparable_overfield
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (X : (Spec (.of K)).Etale)
    (x : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
    (z : Γ(X.left, ⊤)) :
    IsSeparable K ((ΓSpecIso (.of Ω)).hom (x.left.appTop z)) := by
  classical
  let S := Spec (.of K)
  let y := x.left (IsLocalRing.closedPoint Ω)
  let q := X.hom y
  have hq : IsClosed ({q} : Set S) := by
    have : ({q} : Set S) = Set.univ := Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
    rw [this]
    exact isClosed_univ
  have : IsClosedImmersion (S.fromSpecResidueField q) :=
    isClosed_singleton_iff_isClosedImmersion.mp hq
  have : Surjective (S.fromSpecResidueField q) :=
    ⟨fun t ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  have : IsIso (S.fromSpecResidueField q) :=
    isIso_of_isClosedImmersion_of_surjective _
  let b : CommRingCat.of K ⟶ S.residueField q :=
    Spec.preimage (S.fromSpecResidueField q)
  have : IsIso (Scheme.Spec.map b.op) := by
    change IsIso (Spec.map b)
    dsimp only [b]
    rw [Spec.map_preimage]
    infer_instance
  have : IsIso b.op := isIso_of_reflects_iso b.op Scheme.Spec
  have : IsIso b := isIso_of_op b
  let m := X.hom.residueFieldMap y
  let a := X.left.descResidueField (stalkClosedPointTo x.left)
  have hb : b.hom.Etale := RingHom.Etale.of_bijective
    (ConcreteCategory.bijective_of_isIso b)
  have hm : m.hom.Etale := X.hom.etale_residueFieldMap y
  let : Algebra K (X.left.residueField y) := (b ≫ m).hom.toAlgebra
  have : Algebra.Etale K (X.left.residueField y) := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact RingHom.Etale.stableUnderComposition _ _ hb hm
  have : Algebra.IsSeparable K (X.left.residueField y) :=
    (Algebra.FormallyEtale.iff_isSeparable K (X.left.residueField y)).mp inferInstance
  have hcomp : b ≫ m ≫ a = CommRingCat.ofHom (algebraMap K Ω) := by
    apply Spec.map_injective
    have hmfac : Spec.map m ≫ S.fromSpecResidueField q =
        X.left.fromSpecResidueField y ≫ X.hom :=
      X.hom.SpecMap_residueFieldMap_fromSpecResidueField y
    have hafac := descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X.left x.left
    calc
      Spec.map (b ≫ m ≫ a) = Spec.map a ≫ (Spec.map m ≫ Spec.map b) := by
        simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map a ≫ (Spec.map m ≫ S.fromSpecResidueField q) := by
        dsimp only [b]
        rw [Spec.map_preimage]
      _ = Spec.map a ≫ (X.left.fromSpecResidueField y ≫ X.hom) := by rw [hmfac]
      _ = x.left ≫ X.hom := by rw [← Category.assoc]; exact congrArg (· ≫ X.hom) hafac
      _ = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := x.w
  let a' : X.left.residueField y →ₐ[K] Ω :=
    { a.hom with
      commutes' r := by
        exact congrArg (fun t : CommRingCat.of K ⟶ CommRingCat.of Ω ↦ t r) hcomp }
  let w := (ΓSpecIso (X.left.residueField y)).hom
    ((X.left.fromSpecResidueField y).appTop z)
  have hw := (Algebra.IsSeparable.isSeparable K w).map a' a'.injective
  have heval : (ΓSpecIso (.of Ω)).hom (x.left.appTop z) = a' w := by
    have hf := descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X.left x.left
    rw [← hf, Hom.comp_appTop]
    exact congrArg (fun t ↦ t ((X.left.fromSpecResidueField y).appTop z))
      (ΓSpecIso_naturality a)
  rw [heval]
  exact hw


/-- Evaluation identifies the additive units stalk with separable-closure units.
The displayed formula fixes the equivalence on every germ, independently of any
equivalence between sheaves and representations.

Source: Stacks Project, Tag 03QV, Example sheaves-point (2), and Morphisms, Tag 02GL.
(blueprint: lem-sc-etale-units-stalk-evaluation-overfield).

Proof: Factor the geometric lift through the residue field of its image.
The structural residue-field extension is etale, hence separable. Naturality of
the global-sections isomorphism shows that evaluation of every function is
separable over K. The given embedding of Ks into Omega corestricts to the relative
separable closure of K in Omega. This is bijective because both fields are
separable closures of K. Its inverse is determined by the given embedding.
Compose the evaluation ring map into the relative separable closure with this
inverse, then take units, write them additively, and use ULift. Injectivity of
Ks -> Omega and compatibility of pullback of global functions prove that these
maps form a compatible cocone on pointed etale neighbourhoods. The colimit
descending map followed by ULift.down is the additive evaluation homomorphism.
The cocone identities give its formula on every germ. Apply the independent
bijectivity theorem to obtain the additive equivalence, with the same formula.
No arbitrary data come from an unproved existence statement: the field equivalence
and the colimit map are constructed from proved universal properties. The proof
works for imperfect K and does not assume Omega/K algebraic. -/
theorem exists_etaleUnits_stalk_evaluation_overfield
    (K Ω : Type u) [Field K] [Field Ω]
    [Algebra (SeparableClosure K) Ω] [Algebra K Ω]
    [IsScalarTower K (SeparableClosure K) Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∃ e : ↑((p.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S.gmSheaf) ≃+
        Additive (SeparableClosure K)ˣ,
      ∀ (X : S.Etale) (x : p.fiber.obj X) (z : S.gmSheaf.obj.obj (op X)),
        algebraMap (SeparableClosure K) Ω
          (↑(Additive.toMul (e (p.toPresheafFiber X x S.gmSheaf.obj z)))) =
            (ΓSpecIso (.of Ω)).hom
              (x.left.appTop ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤))) := by
  classical
  dsimp only
  let Ks := SeparableClosure K
  let S := Spec (.of K)
  let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  let j : Ks →ₐ[K] separableClosure K Ω :=
    { toFun := fun t ↦ ⟨algebraMap Ks Ω t,
        (Algebra.IsSeparable.isSeparable K t).map
          (IsScalarTower.toAlgHom K Ks Ω) (algebraMap Ks Ω).injective⟩
      map_one' := Subtype.ext (map_one (algebraMap Ks Ω))
      map_mul' a b := Subtype.ext (map_mul (algebraMap Ks Ω) a b)
      map_zero' := Subtype.ext (map_zero (algebraMap Ks Ω))
      map_add' a b := Subtype.ext (map_add (algebraMap Ks Ω) a b)
      commutes' t := Subtype.ext (IsScalarTower.algebraMap_apply K Ks Ω t).symm }
  let c : Ks ≃ₐ[K] separableClosure K Ω := AlgEquiv.ofBijective j
    (Algebra.IsAlgebraic.algHom_bijective₂ j
      (IsSepClosed.lift : separableClosure K Ω →ₐ[K] Ks)).1
  let ev (X : S.Etale) (x : p.fiber.obj X) : Γ(X.left, ⊤) →+* Ω :=
    (x.left.appTop ≫ (ΓSpecIso (.of Ω)).hom).hom
  let evRel (X : S.Etale) (x : p.fiber.obj X) :
      Γ(X.left, ⊤) →+* separableClosure K Ω :=
    { toFun := fun z ↦ ⟨ev X x z, evaluation_isSeparable_overfield K Ω X x z⟩
      map_one' := Subtype.ext (map_one (ev X x))
      map_mul' a b := Subtype.ext (map_mul (ev X x) a b)
      map_zero' := Subtype.ext (map_zero (ev X x))
      map_add' a b := Subtype.ext (map_add (ev X x) a b) }
  let evKs (X : S.Etale) (x : p.fiber.obj X) : Γ(X.left, ⊤) →+* Ks :=
    c.symm.toRingHom.comp (evRel X x)
  have hev (X : S.Etale) (x : p.fiber.obj X) (z : Γ(X.left, ⊤)) :
      algebraMap Ks Ω (evKs X x z) = ev X x z :=
    congrArg Subtype.val (c.apply_symm_apply (evRel X x z))
  let φ (X : S.Etale) (x : p.fiber.obj X) :
      S.gmSheaf.obj.obj (op X) ⟶
        AddCommGrpCat.of (ULift.{u + 1} (Additive Ksˣ)) :=
    AddCommGrpCat.ofHom
      { toFun := fun z ↦ ULift.up (Additive.ofMul (Units.map (evKs X x).toMonoidHom
          (Additive.toMul z.down)))
        map_zero' := by apply ULift.ext; simp
        map_add' a b := by apply ULift.ext; simp }
  have hφ : ∀ ⦃X Y : S.Etale⦄ (a : X ⟶ Y) (x : p.fiber.obj X),
      S.gmSheaf.obj.map a.op ≫ φ X x = φ Y (p.fiber.map a x) := by
    intro X Y a x
    apply AddCommGrpCat.ext
    intro z
    apply ULift.ext
    apply Additive.toMul.injective
    apply Units.ext
    apply (algebraMap Ks Ω).injective
    change algebraMap Ks Ω
        (evKs X x (a.left.appTop ((Additive.toMul z.down : Γ(Y.left, ⊤)ˣ) : Γ(Y.left, ⊤)))) =
      algebraMap Ks Ω
        (evKs Y (p.fiber.map a x) ((Additive.toMul z.down : Γ(Y.left, ⊤)ˣ) : Γ(Y.left, ⊤)))
    rw [hev, hev]
    dsimp [ev, p, pointSmallEtale]
    rfl
  let fLift := p.presheafFiberDesc φ hφ
  let f : ↑((p.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S.gmSheaf) →+ Additive Ksˣ :=
    { toFun := fun z ↦ (fLift z).down
      map_zero' := by simp
      map_add' a b := by simp }
  have hf (X : S.Etale) (x : p.fiber.obj X) (z : S.gmSheaf.obj.obj (op X)) :
      algebraMap Ks Ω (↑(Additive.toMul (f (p.toPresheafFiber X x S.gmSheaf.obj z)))) =
        (ΓSpecIso (.of Ω)).hom
          (x.left.appTop ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤))) := by
    have h := congrArg ULift.down <| ConcreteCategory.congr_hom
      (p.toPresheafFiber_presheafFiberDesc φ hφ X x) z
    change algebraMap Ks Ω
        (Additive.toMul (fLift (p.toPresheafFiber X x S.gmSheaf.obj z)).down : Ksˣ) = _
    calc
      _ = algebraMap Ks Ω (evKs X x
          ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤))) :=
        congrArg (fun t : Additive Ksˣ ↦ algebraMap Ks Ω (Additive.toMul t : Ksˣ)) h
      _ = _ := hev X x _
  exact ⟨AddEquiv.ofBijective f
    (etaleUnits_stalk_evaluation_overfield_bijective K Ω f hf), hf⟩

end AlgebraicGeometry.Scheme
