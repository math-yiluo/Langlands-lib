/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# The affine scheme of roots of unity

Source: Stacks Project, groupoids.tex, Tag 040M, Example `example-roots-of-unity`,
and etale-cohomology.tex, Tag 03PK, Section `section-kummer`
(blueprint: lem-asd-affine-roots-representability).

## Main definitions

- `affineRootsOver`: the explicit quotient spectrum over `Spec R`.
- `affineRootsCoordinate`: its distinguished global section.

## Main statement

- `affineRoots_representability`: the natural bijections, their sheaf identification, and
  their compatibility with arbitrary base change.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Polynomial

namespace AlgebraicGeometry

/-- The scheme `Spec R[t]/(t^n - 1)` over `Spec R`. `AdjoinRoot` is exactly the quotient
by the principal ideal, and the structure morphism is induced by the quotient algebra map.
Source: Stacks, Tag 040M (blueprint: lem-asd-affine-roots-representability). -/
noncomputable def affineRootsOver (R : Type u) [CommRing R] (n : ℕ) :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R
    (AdjoinRoot ((X : R[X]) ^ n - 1)))))

/-- The global section corresponding to the residue class of `t` in `R[t]/(t^n - 1)`.
Source: Stacks, Tag 040M (blueprint: lem-asd-affine-roots-representability). -/
noncomputable def affineRootsCoordinate (R : Type u) [CommRing R] (n : ℕ) :
    Γ((affineRootsOver R n).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot ((X : R[X]) ^ n - 1)))).inv
    (AdjoinRoot.root ((X : R[X]) ^ n - 1))

private lemma coordinate_pow (R : Type u) [CommRing R] (n : ℕ) :
    affineRootsCoordinate R n ^ n = 1 := by
  have h : AdjoinRoot.root ((X : R[X]) ^ n - 1) ^ n = 1 := by
    have h := AdjoinRoot.eval₂_root ((X : R[X]) ^ n - 1)
    simpa only [eval₂_sub, eval₂_X_pow, eval₂_one, sub_eq_zero] using h
  change (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot ((X : R[X]) ^ n - 1)))).inv.hom
    (AdjoinRoot.root ((X : R[X]) ^ n - 1)) ^ n = 1
  rw [← map_pow, h, map_one]

set_option backward.isDefEq.respectTransparency false in
private lemma roots_hom_ext (R : Type u) [CommRing R] (n : ℕ)
    {U : Over (Spec (CommRingCat.of R))} (a b : U ⟶ affineRootsOver R n)
    (h : a.left.appTop (affineRootsCoordinate R n) =
      b.left.appTop (affineRootsCoordinate R n)) : a = b := by
  apply Over.OverMorphism.ext
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  apply AdjoinRoot.ringHom_ext
  · have ha := congrArg Scheme.Hom.appTop (Over.w a)
    have hb := congrArg Scheme.Hom.appTop (Over.w b)
    simp only [Scheme.Hom.comp_appTop] at ha hb
    have hab := ha.trans hb.symm
    have hab' := congrArg (fun f ↦ (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f) hab
    simp only [affineRootsOver, Over.mk_hom, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality] at hab'
    exact congrArg CommRingCat.Hom.hom hab'
  · exact h

set_option backward.isDefEq.respectTransparency false in
private lemma roots_hom_exists (R : Type u) [CommRing R] (n : ℕ)
    (U : Over (Spec (CommRingCat.of R))) (z : Γ(U.left, ⊤)) (hz : z ^ n = 1) :
    ∃ a : U ⟶ affineRootsOver R n,
      a.left.appTop (affineRootsCoordinate R n) = z := by
  let ρ : CommRingCat.of R ⟶ Γ(U.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ U.hom.appTop
  have hz' : eval₂ ρ.hom z ((X : R[X]) ^ n - 1) = 0 := by simp [hz]
  let φ : CommRingCat.of (AdjoinRoot ((X : R[X]) ^ n - 1)) ⟶ Γ(U.left, ⊤) :=
    CommRingCat.ofHom (AdjoinRoot.lift ρ.hom z hz')
  let a : U.left ⟶ Spec (CommRingCat.of (AdjoinRoot ((X : R[X]) ^ n - 1))) :=
    ΓSpec.adjunction.homEquiv U.left _ φ.op
  have ha : (Scheme.ΓSpecIso _).inv ≫ a.appTop = φ :=
    ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ
  have hw : a ≫ (affineRootsOver R n).hom = U.hom := by
    apply ext_to_Spec
    change (Scheme.ΓSpecIso _).inv ≫ (a ≫ (affineRootsOver R n).hom).appTop = _
    rw [Scheme.Hom.comp_appTop, ← Category.assoc]
    change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R _))).appTop ≫ a.appTop = ρ
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
    rw [ha]
    apply CommRingCat.hom_ext
    exact AdjoinRoot.lift_comp_of hz'
  refine ⟨Over.homMk a hw, ?_⟩
  change ((Scheme.ΓSpecIso _).inv ≫ a.appTop) (AdjoinRoot.root _) = z
  rw [ha]
  exact AdjoinRoot.lift_root hz'

private theorem roots_sections_equiv (S : Scheme.{u}) (n : ℕ) (U : S.Etaleᵒᵖ) :
    ∃ k : (S.rootsOfUnitySheaf n).obj.obj U ≃
        {z : Γ(U.unop.left, ⊤)ˣ // z ^ n = 1},
      ∀ y, (k y).val =
        Additive.toMul (((kernel.ι (n • 𝟙 S.gmSheaf)).hom.app U y).down) := by
  let ev := sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj U
  let φ := ev.map (n • 𝟙 S.gmSheaf)
  let e := PreservesKernel.iso ev (n • 𝟙 S.gmSheaf) ≪≫ AddCommGrpCat.kernelIsoKer φ
  let g : φ.hom.ker ≃ {z : Γ(U.unop.left, ⊤)ˣ // z ^ n = 1} :=
    { toFun := fun y ↦ ⟨y.1.down.toMul, by
        have hy : n • y.1 = 0 := y.2
        exact congrArg (fun z ↦ z.down.toMul) hy⟩
      invFun := fun z ↦ ⟨ULift.up (Additive.ofMul z.val), by
        change n • (ULift.up (Additive.ofMul z.val)) = 0
        apply ULift.ext
        apply Additive.toMul.injective
        exact z.property⟩
      left_inv := fun y ↦ rfl
      right_inv := fun z ↦ rfl }
  refine ⟨e.addCommGroupIsoToAddEquiv.toEquiv.trans g, ?_⟩
  intro y
  have he : e.hom ≫ AddCommGrpCat.ofHom φ.hom.ker.subtype =
      ev.map (kernel.ι (n • 𝟙 S.gmSheaf)) := by
    rw [Iso.trans_hom, Category.assoc, AddCommGrpCat.kernelIsoKer_hom_comp_subtype,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
  exact congrArg (fun z ↦ z.down.toMul) (ConcreteCategory.congr_hom he y)

set_option backward.isDefEq.respectTransparency false in
/-- The affine root scheme represents roots of unity on all test schemes, naturally and
compatibly with arbitrary base change. The presheaf isomorphism is the identification of
sheaves: the left side is a sheaf by `smallEtaleRepresentablePresheaf_isSheaf`, and the right
side is the underlying presheaf of the recorded roots sheaf. The representable presheaf is
transported by the standard `ULift` functor to the coefficient universe `u+1`. The formula
is specified using
the kernel inclusion into `gmSheaf`, whose sections are lifted, additively written units.
Mathlib's `Over.pullback` chooses `P ×_V V'`, with projection `pullback.fst` to `P`, for the
base change denoted `V' ×_V P` in the source.

Source: Stacks, Tag 040M and Tag 03PK
(blueprint: lem-asd-affine-roots-representability).

Proof: The quotient relation gives `x^n = 1`, so `x` is a unit with inverse `x^(n-1)`.
The adjunction between global sections and affine spectra identifies a morphism into `P`
with a ring homomorphism from `R[t]/(t^n-1)` to the global section ring. Being over `Spec R`
means this homomorphism is an `R`-algebra homomorphism. The polynomial and quotient universal
properties identify these homomorphisms with sections whose nth power is one, which are
units because n is positive. This correspondence sends a morphism to pullback of `x`.
Functoriality of pullback gives naturality in every test scheme. Restrict to the small
etale site; the representable presheaf is a sheaf by
`lem-weil-pbc-small-etale-representable-presheaf-sheaf`, and the kernel definition of
`def-asd-etale-roots-of-unity` gives precisely the same roots and restriction maps. This
produces the displayed presheaf isomorphism with its specified kernel-inclusion formula.
Finally, the fibre-product universal property identifies morphisms into the base-changed
scheme with morphisms into `P` over `V`; applying the same correspondence gives the
base-changed bijections. Composition of pullbacks gives their naturality and the final
compatibility with base-changing a morphism. -/
theorem affineRoots_representability (R : Type u) [CommRing R] (n : ℕ) (hn : 1 ≤ n) :
    ∃ x : Γ((affineRootsOver R n).left, ⊤)ˣ,
      (x : Γ((affineRootsOver R n).left, ⊤)) = affineRootsCoordinate R n ∧
      ((x⁻¹ : Γ((affineRootsOver R n).left, ⊤)ˣ) :
          Γ((affineRootsOver R n).left, ⊤)) = affineRootsCoordinate R n ^ (n - 1) ∧
      ∃ E : ∀ U : Over (Spec (CommRingCat.of R)),
          (U ⟶ affineRootsOver R n) ≃ {z : Γ(U.left, ⊤)ˣ // z ^ n = 1},
        (∀ (U : Over (Spec (CommRingCat.of R))) (a : U ⟶ affineRootsOver R n),
          ((E U a).val : Γ(U.left, ⊤)) = a.left.appTop (affineRootsCoordinate R n)) ∧
        (∀ (U W : Over (Spec (CommRingCat.of R))) (f : U ⟶ W)
            (a : W ⟶ affineRootsOver R n),
          (E U (f ≫ a)).val = Units.map f.left.appTop.hom.toMonoidHom (E W a).val) ∧
        (∃ e : ((Scheme.Etale.forget (Spec (CommRingCat.of R))).op ⋙
              yoneda.obj (affineRootsOver R n) ⋙ uliftFunctor.{u + 1, u}) ≅
            ((Spec (CommRingCat.of R)).rootsOfUnitySheaf n).obj ⋙
              forget AddCommGrpCat.{u + 1},
          ∀ (W : (Spec (CommRingCat.of R)).Etale)
              (a : (Scheme.Etale.forget _).obj W ⟶ affineRootsOver R n),
            Additive.toMul
              (((kernel.ι (n • 𝟙 (Spec (CommRingCat.of R)).gmSheaf)).hom.app (op W)
                (e.hom.app (op W) ⟨a⟩)).down) =
              (E ((Scheme.Etale.forget _).obj W) a).val) ∧
        (∀ (V' : Scheme.{u}) (v : V' ⟶ Spec (CommRingCat.of R)),
          ∃ E' : ∀ U : Over V',
              (U ⟶ (Over.pullback v).obj (affineRootsOver R n)) ≃
                {z : Γ(U.left, ⊤)ˣ // z ^ n = 1},
            (∀ (U : Over V') (a : U ⟶ (Over.pullback v).obj (affineRootsOver R n)),
              ((E' U a).val : Γ(U.left, ⊤)) = a.left.appTop
                ((pullback.fst (affineRootsOver R n).hom v).appTop
                  (affineRootsCoordinate R n))) ∧
            (∀ (U W : Over V') (f : U ⟶ W)
                (a : W ⟶ (Over.pullback v).obj (affineRootsOver R n)),
              (E' U (f ≫ a)).val = Units.map f.left.appTop.hom.toMonoidHom (E' W a).val) ∧
            (∀ (U : Over (Spec (CommRingCat.of R))) (a : U ⟶ affineRootsOver R n),
              (E' ((Over.pullback v).obj U) ((Over.pullback v).map a)).val =
                Units.map (pullback.fst U.hom v).appTop.hom.toMonoidHom (E U a).val)) := by
  classical
  have hp := coordinate_pow R n
  let x : Γ((affineRootsOver R n).left, ⊤)ˣ :=
    ⟨affineRootsCoordinate R n, affineRootsCoordinate R n ^ (n - 1),
      by rw [← pow_succ', Nat.sub_add_cancel hn, hp],
      by rw [← pow_succ, Nat.sub_add_cancel hn, hp]⟩
  let F (U : Over (Spec (CommRingCat.of R))) (a : U ⟶ affineRootsOver R n) :
      {z : Γ(U.left, ⊤)ˣ // z ^ n = 1} :=
    ⟨Units.map a.left.appTop.hom.toMonoidHom x, by
      apply Units.ext
      change a.left.appTop (affineRootsCoordinate R n) ^ n = 1
      rw [← map_pow, hp, map_one]⟩
  have hF (U : Over (Spec (CommRingCat.of R))) : Function.Bijective (F U) := by
    constructor
    · intro a b hab
      apply roots_hom_ext R n a b
      exact congrArg (fun z ↦ (z.val : Γ(U.left, ⊤))) hab
    · intro z
      obtain ⟨a, ha⟩ := roots_hom_exists R n U z.val (congrArg Units.val z.property)
      refine ⟨a, ?_⟩
      apply Subtype.ext
      apply Units.ext
      exact ha
  let E := fun U ↦ Equiv.ofBijective (F U) (hF U)
  have hE (U) (a : U ⟶ affineRootsOver R n) :
      ((E U a).val : Γ(U.left, ⊤)) = a.left.appTop (affineRootsCoordinate R n) := rfl
  have hnat (U W) (f : U ⟶ W) (a : W ⟶ affineRootsOver R n) :
      (E U (f ≫ a)).val = Units.map f.left.appTop.hom.toMonoidHom (E W a).val := by
    apply Units.ext
    change (f.left ≫ a.left).appTop _ = f.left.appTop (a.left.appTop _)
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  refine ⟨x, rfl, rfl, E, hE, hnat, ?_, ?_⟩
  · let S := Spec (CommRingCat.of R)
    choose k hk using fun U : S.Etaleᵒᵖ ↦ roots_sections_equiv S n U
    have hk_symm (U : S.Etaleᵒᵖ) (z : {z : Γ(U.unop.left, ⊤)ˣ // z ^ n = 1}) :
        Additive.toMul
          (((kernel.ι (n • 𝟙 S.gmSheaf)).hom.app U ((k U).symm z)).down) = z.val := by
      simpa only [Equiv.apply_symm_apply] using (hk U ((k U).symm z)).symm
    have hi (U W : S.Etaleᵒᵖ) (f : U ⟶ W)
        (y : (S.rootsOfUnitySheaf n).obj.obj U) :
        Additive.toMul (((kernel.ι (n • 𝟙 S.gmSheaf)).hom.app W
          ((S.rootsOfUnitySheaf n).obj.map f y)).down) =
          Units.map f.unop.left.appTop.hom.toMonoidHom
            (Additive.toMul (((kernel.ι (n • 𝟙 S.gmSheaf)).hom.app U y).down)) := by
      exact congrArg (fun z ↦ z.down.toMul)
        (ConcreteCategory.congr_hom ((kernel.ι (n • 𝟙 S.gmSheaf)).hom.naturality f) y)
    let c (W : S.Etaleᵒᵖ) :
        ULift.{u + 1} ((Scheme.Etale.forget S).obj W.unop ⟶ affineRootsOver R n) ≃
          (S.rootsOfUnitySheaf n).obj.obj W :=
      (Equiv.ulift.trans (E ((Scheme.Etale.forget S).obj W.unop))).trans (k W).symm
    refine ⟨NatIso.ofComponents (fun W ↦ (c W).toIso) ?_, ?_⟩
    · intro U W f
      ext a
      apply (k W).injective
      apply Subtype.ext
      change (k W ((k W).symm
        (E _ ((Scheme.Etale.forget S).map f.unop ≫ a.down)))).val =
          (k W ((S.rootsOfUnitySheaf n).obj.map f
            ((k U).symm (E _ a.down)))).val
      rw [Equiv.apply_symm_apply, hk, hi]
      refine (hnat _ _ ((Scheme.Etale.forget S).map f.unop) a.down).trans ?_
      exact congrArg (Units.map f.unop.left.appTop.hom.toMonoidHom)
        (hk_symm U (E _ a.down)).symm
    · intro W a
      exact hk_symm (op W) (E _ a)
  · intro V' v
    let E' (U : Over V') :
        (U ⟶ (Over.pullback v).obj (affineRootsOver R n)) ≃
          {z : Γ(U.left, ⊤)ˣ // z ^ n = 1} :=
      ((Over.mapPullbackAdj v).homEquiv U (affineRootsOver R n)).symm.trans
        (E ((Over.map v).obj U))
    have hE' (U : Over V') (a : U ⟶ (Over.pullback v).obj (affineRootsOver R n)) :
        ((E' U a).val : Γ(U.left, ⊤)) = a.left.appTop
          ((pullback.fst (affineRootsOver R n).hom v).appTop
            (affineRootsCoordinate R n)) := by
      change (E _ (((Over.mapPullbackAdj v).homEquiv U _).symm a)).val.val = _
      rw [hE]
      change (a.left ≫ pullback.fst _ _).appTop _ = _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rfl
    refine ⟨E', hE', ?_, ?_⟩
    · intro U W f a
      apply Units.ext
      rw [hE']
      change _ = f.left.appTop ((E' W a).val : Γ(W.left, ⊤))
      rw [hE']
      change (f.left ≫ a.left).appTop _ = _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    · intro U a
      apply Units.ext
      rw [hE']
      change _ = (pullback.fst U.hom v).appTop ((E U a).val : Γ(U.left, ⊤))
      rw [hE]
      have hpb : ((Over.pullback v).map a).left ≫
          pullback.fst (affineRootsOver R n).hom v = pullback.fst U.hom v ≫ a.left := by
        simp only [Over.pullback_map_left, pullback.lift_fst]
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        Over.pullback_obj_left] using
        ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hpb) (affineRootsCoordinate R n)

end AlgebraicGeometry
