/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.BalancedActionQuasicoherentRealization
/-! # Quasi-coherent realization of a graded action

Source: Stacks Project, Tag 0897, relative-spectrum construction; Tags 01LX and 01SB.
(blueprint: lem-weil-pbc-graded-module-quasicoherent-realization).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry

/-- A quasi-coherent graded action has a geometric realization, without a finiteness
assumption on its homogeneous generators, the algebra, or the base.

Source: Stacks Project, Tag 0897, relative-spectrum construction, using 01LX and 01SB.
(blueprint: lem-weil-pbc-graded-module-quasicoherent-realization).

Proof: On an affine open U = Spec C of X take the direct sum of the modules of
sections G_m(U). The internal decomposition of B extends the homogeneous maps mu
uniquely by finite sums to a B-action on this direct sum. Additivity of mu and its
multiplication law imply the module laws. The scalar formula identifies the A-action
with the action through A -> C; taking a = 1 gives the identity action. The commuting
C-action therefore extends to C tensor_A B. Quasi-coherence identifies restrictions
on affine basic opens with localization. Localization commutes with direct sums and
with the homogeneous action, so these local modules and actions agree on overlaps.
They glue to a quasi-coherent module over the pulled-back algebra sheaf. Relative
Spec base change identifies its spectrum with Y; affine module correspondence gives
F and an algebra-linear identification of its pushforward with that module. After
restriction of scalars, the homogeneous inclusions give the coproduct cocone iota.
On each affine open the action of b on the m-th summand is mu m k b, hence its
inclusion equals inclusion followed by multiplication by fB^sharp(b). Equality of
sheaf maps can be checked on the affine cover, giving the asserted global formula.
The construction uses no finite generators and works for zero summands and empty X. -/
theorem gradedModule_quasicoherent_realization
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {x y : B}, x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l))
    (hscalar : ∀ (a : A), algebraMap A B a ∈ graded 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (G : ℕ → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hG : ∀ m : ℕ, (G m).IsQuasicoherent)
    (mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)))
    (hmu_add : ∀ (m k : ℕ) (b b' : graded k),
      mu m k (b + b') = mu m k b + mu m k b')
    (hmu_mul : ∀ (m k l : ℕ) (b : graded k) (b' : graded l),
      HEq (mu m l b' ≫ mu (m + l) k b)
        (mu m (k + l) ⟨b.val * b'.val, hmul k l b.property b'.property⟩))
    (hmu_scalar : ∀ (m : ℕ) (a : A) (U : X.Opens)
      (t : (G m).val.obj (op U)),
      HEq ((mu m 0 ⟨algebraMap A B a, hscalar a⟩).val.app (op U) t)
        ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) • t))
    :
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let Y := pullback f g
    let pi : Y ⟶ X := pullback.fst f g
    let fB : Y ⟶ Spec (.of B) := pullback.snd f g
    ∃ (F : Y.Modules), F.IsQuasicoherent ∧
      ∃ (iota : ∀ m : ℕ, G m ⟶ (Scheme.Modules.pushforward pi).obj F),
        Nonempty (IsColimit (Cofan.mk ((Scheme.Modules.pushforward pi).obj F) iota)) ∧
          ∀ (k m : ℕ) (b : graded k),
            mu m k b ≫ iota (m + k) = iota m ≫
              (Scheme.Modules.pushforward pi).map
                (F.smulHom (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b.val)) := by
  classical
  -- Use the scheme-module interface for its category and scalar endomorphisms.
  let G : ℕ → X.Modules := G
  let _ : ∀ m, (G m).IsQuasicoherent := hG
  let M : X.Modules := ∐ G
  -- The existing closure theorem indexes in Type u; reindex the countable sum.
  have hM : M.IsQuasicoherent := by
    let G' : ULift.{u} ℕ → X.Modules := fun m ↦ G m.down
    have : (∐ G').IsQuasicoherent := Scheme.Modules.isQuasicoherent_sigma G'
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Sigma.reindex Equiv.ulift G) this
  let i (m : ℕ) : G m ⟶ M := Sigma.ι G m
  let muAdd (m k : ℕ) : graded k →+ (G m ⟶ G (m + k)) :=
    { toFun := mu m k
      map_add' := hmu_add m k
      map_zero' := by
        apply add_left_cancel (a := mu m k 0)
        simpa only [add_zero] using (hmu_add m k 0 0).symm }
  -- Extend homogeneous maps by the sheaf coproduct universal property.
  let T (k : ℕ) : graded k →+ End M :=
    { toFun := fun b ↦ .of (Sigma.desc (fun m ↦ mu m k b ≫ i (m + k)))
      map_zero' := by
        apply End.ext
        apply Sigma.hom_ext
        intro m
        change Sigma.ι G m ≫ Sigma.desc _ = Sigma.ι G m ≫ 0
        rw [Sigma.ι_comp_desc, show mu m k 0 = 0 from (muAdd m k).map_zero]
        simp
      map_add' := by
        intro b c
        apply End.ext
        apply Sigma.hom_ext
        intro m
        change Sigma.ι G m ≫ Sigma.desc _ =
          Sigma.ι G m ≫ (Sigma.desc _ + Sigma.desc _)
        rw [Preadditive.comp_add, Sigma.ι_comp_desc, Sigma.ι_comp_desc, Sigma.ι_comp_desc,
          hmu_add, Preadditive.add_comp] }
  have hT (k m : ℕ) (b : graded k) :
      i m ≫ (T k b).asHom = mu m k b ≫ i (m + k) := by
    exact Sigma.ι_comp_desc _ m
  have transport {m n n' : ℕ} (hn : n = n')
      {q : G m ⟶ G n} {q' : G m ⟶ G n'} (hq : HEq q q') :
      q ≫ i n = q' ≫ i n' := by
    subst n'
    cases hq
    rfl
  have hTscalar (a : A) :
      T 0 ⟨algebraMap A B a, hscalar a⟩ =
        .of (M.smulHom (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a)) := by
    apply End.ext
    apply Sigma.hom_ext
    intro m
    rw [hT, ← Scheme.Modules.smulHom_naturality]
    have hm : mu m 0 ⟨algebraMap A B a, hscalar a⟩ =
        (G m).smulHom (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) := by
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      exact eq_of_heq (hmu_scalar m a U.unop t)
    exact congrArg (fun q ↦ q ≫ i m) hm
  have hTunit : T 0 ⟨1, hunit⟩ = 1 := by
    apply End.ext
    simpa only [End.one_asHom, map_one, Scheme.Modules.smulHom_one] using
      congrArg End.asHom (hTscalar 1)
  have hTmul (k l : ℕ) (b : graded k) (c : graded l) :
      T (k + l) ⟨b.val * c.val, hmul k l b.property c.property⟩ = T k b * T l c := by
    apply End.ext
    apply Sigma.hom_ext
    intro m
    change i m ≫ _ = i m ≫ ((T l c).asHom ≫ (T k b).asHom)
    rw [hT, ← Category.assoc, hT, Category.assoc, hT, ← Category.assoc]
    exact (transport (by omega : m + l + k = m + (k + l))
      (hmu_mul m k l b c)).symm
  -- Internal grading identifies B with finite sums of homogeneous scalars.
  let e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap graded) hgrading).toAddEquiv
  let act : B →+ End M := (DirectSum.toAddMonoid T).comp e.symm.toAddMonoidHom
  have he (k : ℕ) (b : graded k) : e (DirectSum.of (fun k ↦ graded k) k b) = b.val := by
    exact DirectSum.coeLinearMap_of graded k b
  have hact (k : ℕ) (b : graded k) : act b.val = T k b := by
    rw [← he k b]
    simp [act]
  have hactmul (b c : B) : act (b * c) = act b * act c := by
    obtain ⟨b, rfl⟩ := e.surjective b
    obtain ⟨c, rfl⟩ := e.surjective c
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, add_mul, hb, hb']
    | of k b =>
      induction c using DirectSum.induction_on with
      | zero => simp
      | add c c' hc hc' => simp only [map_add, mul_add, hc, hc']
      | of l c =>
        rw [he, he]
        exact (hact (k + l) ⟨b.val * c.val, hmul k l b.property c.property⟩).trans
          ((hTmul k l b c).trans (by rw [hact, hact]))
  let rho : B →+* End M :=
    { act with
      map_one' := (hact 0 ⟨1, hunit⟩).trans hTunit
      map_mul' := hactmul }
  have hbalance (a : A) : rho (algebraMap A B a) =
      .of (M.smulHom (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a)) :=
    (hact 0 ⟨algebraMap A B a, hscalar a⟩).trans (hTscalar a)
  -- Geometry now uses only the balanced B-action, without the grading.
  obtain ⟨F, hF, iso, hiso⟩ := balancedAction_quasicoherent_realization f M hM rho hbalance
  refine ⟨F, hF, (fun m ↦ i m ≫ iso.hom), ?_, ?_⟩
  · exact ⟨Cofan.IsColimit.mk _
      (fun c ↦ iso.inv ≫ Sigma.desc (fun m ↦ c.inj m))
      (by intro c m; simp [i])
      (by
        intro c q hq
        apply (cancel_epi iso.hom).mp
        apply Sigma.hom_ext
        intro m
        simpa [i] using hq m)⟩
  · intro k m b
    change mu m k b ≫ (i (m + k) ≫ iso.hom) = _
    rw [← Category.assoc, ← hT, Category.assoc]
    rw [← hact]
    change i m ≫ ((rho b.val).asHom ≫ iso.hom) = _
    rw [hiso, ← Category.assoc]


end AlgebraicGeometry
