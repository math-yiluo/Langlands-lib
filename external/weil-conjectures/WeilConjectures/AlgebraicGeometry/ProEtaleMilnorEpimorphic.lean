/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits

/-!
# Epimorphic towers on the pro-etale site

Source: the Weil conjectures blueprint, main-20261015, `chap-The-pro-etale-site`,
`proposition-milnor-sequence`, lemma `proposition-milnor-sequence--3`
(blueprint: proposition-milnor-sequence--3).

## Main declarations

* `milnorLimitProjection`: the tuple of the limit projections, in degree zero.
* `milnorLimitComparison_condition`: its zero-null-homotopy condition.
* `milnorLimitComparison`: the canonical map to the recorded Roos complex.
* `milnor_epimorphic`: all three conclusions for an epimorphic tower.

The derived limit is exactly `WeilConjectures.integralOperationsRoos`, as in
`AlgebraicGeometry.Scheme.ProEt.milnor_sequence`, not a new cone construction.
-/

@[expose] public section

set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe v u t w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The tuple of the ordinary limit projections, embedded in degree zero.

Source: the Weil conjectures blueprint, main-20261015, `proposition-milnor-sequence`,
`proposition-milnor-sequence--3` (blueprint: proposition-milnor-sequence--3). -/
noncomputable def milnorLimitProjection
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableProducts C]
    (M : ℕᵒᵖ ⥤ C) [HasLimit M] :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (limit M) ⟶
      ∏ᶜ (fun n : ℕ ↦ (Scheme.ProEt.milnorSingleTower M).obj (op n)) :=
  Pi.lift (fun n : ℕ ↦
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (limit.π M (op n)))

/-- The tuple of limit projections admits the zero null-homotopy for `1 - T`.

Source: the Weil conjectures blueprint, main-20261015, `proposition-milnor-sequence`,
`proposition-milnor-sequence--3` (blueprint: proposition-milnor-sequence--3).

Proof: compose with the nth product projection. The composite with `1 - T` is
`p_n - p_(n+1) t_n = 0` by the limit cone equation, after applying the additive
single-complex functor. Product extensionality gives zero. The differential of
the zero cochain is zero, giving the displayed cocycle condition. -/
theorem milnorLimitComparison_condition
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableProducts C]
    (M : ℕᵒᵖ ⥤ C) [HasLimit M] :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (limit M))
          (∏ᶜ (fun n : ℕ ↦ (Scheme.ProEt.milnorSingleTower M).obj (op n))) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (milnorLimitProjection M ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦ (Scheme.ProEt.milnorSingleTower M).obj (op n))
            (WeilConjectures.integralOperationsTowerStep (Scheme.ProEt.milnorSingleTower M))) =
      0 := by
  have hzero : milnorLimitProjection M ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦ (Scheme.ProEt.milnorSingleTower M).obj (op n))
        (WeilConjectures.integralOperationsTowerStep (Scheme.ProEt.milnorSingleTower M)) =
      0 := by
    apply Pi.hom_ext
    intro n
    simp [milnorLimitProjection, towerTransitionEndomorphism, towerProductShift,
      WeilConjectures.integralOperationsTowerStep, ← Functor.map_comp]
  simp [hzero]

/-- The canonical map from the ordinary limit in degree zero to `Cone(1 - T)[-1]`.
The target is the exact Roos model used by the recorded Milnor sequence. The lift
uses the tuple of actual limit projections and the zero null-homotopy.

Source: the Weil conjectures blueprint, main-20261015, `proposition-milnor-sequence`,
`proposition-milnor-sequence--3` (blueprint: proposition-milnor-sequence--3). -/
noncomputable def milnorLimitComparison
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableProducts C]
    (M : ℕᵒᵖ ⥤ C) [HasLimit M] :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (limit M) ⟶
      WeilConjectures.integralOperationsRoos (Scheme.ProEt.milnorSingleTower M) :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ (Scheme.ProEt.milnorSingleTower M).obj (op n))
      (WeilConjectures.integralOperationsTowerStep (Scheme.ProEt.milnorSingleTower M)))
    (milnorLimitProjection M) 0 (milnorLimitComparison_condition M)

private theorem module_tower_epi
    {A : Type u} [Ring A] (F : ℕ → ModuleCat.{u} A)
    (t : ∀ n, F (n + 1) ⟶ F n) (ht : ∀ n, Epi (t n)) :
    Epi (towerTransitionEndomorphism t) := by
  classical
  apply (ModuleCat.epi_iff_surjective _).2
  intro a
  have hs (n : ℕ) : Function.Surjective (t n) :=
    (ModuleCat.epi_iff_surjective _).1 (ht n)
  choose s hs using fun n x ↦ hs n x
  let b : ∀ n, F n := fun n ↦ Nat.rec (0 : F 0)
    (fun n b ↦ s n (b - Pi.π F n a)) n
  refine ⟨(ModuleCat.piIsoPi F).inv b, ?_⟩
  apply (ModuleCat.mono_iff_injective (ModuleCat.piIsoPi F).hom).1 inferInstance
  funext n
  have hcoord := congrArg
    (fun f : ∏ᶜ F ⟶ F n ↦ f ((ModuleCat.piIsoPi F).inv b))
    ((towerTransitionEndomorphism_eq_iff t _).1 rfl n)
  have hb (n : ℕ) : Pi.π F n ((ModuleCat.piIsoPi F).inv b) = b n := by
    exact congrArg (fun f : ModuleCat.of A (∀ n, F n) ⟶ F n ↦ f b)
      (ModuleCat.piIsoPi_inv_kernel_ι F n)
  have ha : (ModuleCat.piIsoPi F).hom a n = Pi.π F n a := by
    exact congrArg (fun f : ∏ᶜ F ⟶ F n ↦ f a)
      (ModuleCat.piIsoPi_hom_ker_subtype F n)
  change (ModuleCat.piIsoPi F).hom
      ((towerTransitionEndomorphism t) ((ModuleCat.piIsoPi F).inv b)) n = _
  rw [show ∀ x : ↑(∏ᶜ F), (ModuleCat.piIsoPi F).hom x n = Pi.π F n x from
    fun x ↦ congrArg (fun f : ∏ᶜ F ⟶ F n ↦ f x)
      (ModuleCat.piIsoPi_hom_ker_subtype F n), ha]
  have hc : Pi.π F n ((towerTransitionEndomorphism t) ((ModuleCat.piIsoPi F).inv b)) =
      b n - t n (b (n + 1)) := by simpa [hb] using hcoord
  rw [hc]
  change b n - t n (s n (b n - Pi.π F n a)) = Pi.π F n a
  rw [hs]
  exact sub_sub_cancel _ _

private theorem map_transition
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D]
    (E : C ⥤ D) [E.Additive] (F : ℕ → C)
    [HasProduct F] [HasProduct (fun n ↦ E.obj (F n))]
    (t : ∀ n, F (n + 1) ⟶ F n) :
    E.map (towerTransitionEndomorphism t) ≫ piComparison E F =
      piComparison E F ≫ towerTransitionEndomorphism (fun n ↦ E.map (t n)) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, piComparison_comp_π, ← E.map_comp]
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
    Category.id_comp, Pi.lift_comp_π, E.map_sub, E.map_comp, Preadditive.comp_sub,
    Category.assoc, piComparison_comp_π, piComparison_comp_π_assoc]

private theorem sheaf_tower_epi
    (X : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)})
    (M : ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R)
    (ht : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op)) :
    Epi (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
      (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op)) := by
  let F := fun n : ℕ ↦ M.obj (op n)
  let t := fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op
  let S := ShortComplex.mk (towerTransitionEndomorphism t) (0 : ∏ᶜ F ⟶ ∏ᶜ F)
    (by simp)
  apply (S.exact_iff_epi rfl).1
  apply ((Scheme.ProEt.sections_conservative X R).1 _ _ _ _ _ _).2
  intro W hW hw
  have := hW
  let ev := SheafOfModules.evaluation.{max u (t + 1)} R (op W)
  have hpres := peSectionsLimitsColimits.{t, max u (t + 1), 0, 0, 0} R W hw
  have := hpres.1
  have := hpres.2
  have ht' (n : ℕ) : Epi (ev.map (t n)) := by
    have := ht n
    infer_instance
  have he : Epi (towerTransitionEndomorphism
      (K := fun n ↦ ev.obj (F n)) (fun n ↦ ev.map (t n))) :=
    module_tower_epi (fun n ↦ ev.obj (F n)) (fun n ↦ ev.map (t n)) ht'
  have : Epi (ev.map (towerTransitionEndomorphism t) ≫ piComparison ev F) := by
    rw [map_transition]
    infer_instance
  have hmap : Epi (ev.map (towerTransitionEndomorphism t)) :=
    (epi_comp_iff_of_isIso _ (piComparison ev F)).1 inferInstance
  exact ((S.map ev).exact_iff_epi (by simp [S])).2 hmap

private theorem tower_compatibility
    {B : Type*} [Category* B] (F : ℕᵒᵖ ⥤ B) {Z : B}
    (a : ∀ n : ℕ, Z ⟶ F.obj (Opposite.op n))
    (ha : ∀ n, a (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = a n)
    {n m : ℕ} (h : n ≤ m) : a m ≫ F.map (homOfLE h).op = a n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    have he : (homOfLE (Nat.le_trans h (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [he, F.map_comp, ← Category.assoc, ha, ih]

private theorem tower_kernel
    {B : Type*} [Category* B] [Preadditive B]
    (F : ℕᵒᵖ ⥤ B) (c : Cone F) (hc : IsLimit c)
    (P : Fan (fun n : ℕ ↦ F.obj (Opposite.op n))) (hP : IsLimit P)
    (i : c.pt ⟶ P.pt) (t : P.pt ⟶ P.pt)
    (hi : ∀ n : ℕ, i ≫ P.proj n = c.π.app (Opposite.op n))
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj n -
      P.proj (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) :
    ∃ h : i ≫ t = 0, Nonempty (IsLimit (KernelFork.ofι i h)) := by
  have hz : i ≫ t = 0 := by
    apply hP.hom_ext
    intro ⟨n⟩
    change (i ≫ t) ≫ P.proj n = 0 ≫ P.proj n
    rw [Category.assoc, ht, Preadditive.comp_sub, hi, ← Category.assoc, hi]
    simp only [zero_comp, sub_eq_zero]
    exact (c.w (homOfLE (Nat.le_succ n)).op).symm
  refine ⟨hz, ⟨Fork.IsLimit.mk' _ ?_⟩⟩
  intro s
  let Z := s.pt
  let k := s.ι
  have hk : k ≫ t = 0 := by
    have h := s.condition
    simp only [comp_zero] at h
    exact h
  have ha (n : ℕ) : (k ≫ P.proj (n + 1)) ≫
      F.map (homOfLE (Nat.le_succ n)).op = k ≫ P.proj n := by
    have hn := congrArg (fun f ↦ f ≫ P.proj n) hk
    rw [Category.assoc, ht, Preadditive.comp_sub, ← Category.assoc, zero_comp] at hn
    exact (sub_eq_zero.mp hn).symm
  let d : Cone F :=
    { pt := Z
      π := { app := fun n ↦ k ≫ P.proj n.unop
             naturality := by
               intro n m f
               change 𝟙 Z ≫ (k ≫ P.proj m.unop) =
                 (k ≫ P.proj n.unop) ≫ F.map f
               rw [Category.id_comp]
               symm
               exact tower_compatibility F (fun n ↦ k ≫ P.proj n) ha
                 (leOfHom f.unop) } }
  refine ⟨hc.lift d, ?_, ?_⟩
  · apply hP.hom_ext
    intro ⟨n⟩
    change (hc.lift d ≫ i) ≫ P.proj n = k ≫ P.proj n
    rw [Category.assoc, hi]
    exact hc.fac d (Opposite.op n)
  · intro l hl
    apply hc.hom_ext
    intro n
    change l ≫ i = k at hl
    calc
      l ≫ c.π.app n = k ≫ P.proj n.unop := by
        rw [← hi n.unop, ← Category.assoc, hl]
      _ = hc.lift d ≫ c.π.app n := (hc.fac d n).symm

set_option backward.isDefEq.respectTransparency false in
private theorem cocone_lift_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (h : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain S.X₁ S.X₃ (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (S.f ≫ S.g) = 0) :
    QuasiIso (CochainComplex.mappingCocone.lift S.g S.f 0 h) := by
  have hf (p : ℤ) : Epi (S.g.f p) := by
    have := hS.epi_g
    infer_instance
  obtain ⟨κ, hκ, hqκ, _⟩ :=
    CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi S.g hf
  let e := hS.fIsKernel.conePointUniqueUpToIso (kernelIsKernel S.g)
  have he : e.hom ≫ kernel.ι S.g = S.f :=
    hS.fIsKernel.conePointUniqueUpToIso_hom_comp (kernelIsKernel S.g)
      WalkingParallelPair.zero
  have heq : CochainComplex.mappingCocone.lift S.g S.f 0 h = e.hom ≫ κ := by
    ext p
    apply (cancel_mono
      ((CochainComplex.mappingCone S.g).shiftFunctorObjXIso (-1) p (p - 1)
        (by omega)).hom).mp
    apply HomologicalComplex.homotopyCofiber.ext_to_X S.g (p - 1) p
      (by change p - 1 + 1 = p; omega)
    · simp only [Category.assoc, HomologicalComplex.comp_f, (hκ p).2]
      rw [show (e.hom).f p ≫ (kernel.ι S.g).f p = S.f.f p from
        congrArg (fun f ↦ f.f p) he]
      simp only [Int.reduceNeg, CochainComplex.mappingCocone.lift,
        CochainComplex.mappingCocone.liftCocycle, CochainComplex.mappingCocone.liftCochain,
        CochainComplex.mappingCone.liftCochain,
        CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.mappingCone.inl,
        CochainComplex.mappingCone.inr, CochainComplex.HomComplex.Cochain.zero_comp,
        add_zero, CochainComplex.HomComplex.Cocycle.homOf_f,
        CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
          _ _ _ _ p _ _ (p - 1) (by omega),
        CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
        CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.HomComplex.Cochain.mk_v,
        CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
        Iso.refl_inv, Category.assoc, Iso.refl_hom]
      erw [Category.id_comp, Category.id_comp]
      change S.f.f p ≫ HomologicalComplex.homotopyCofiber.inlX S.g p (p - 1) _ ≫
        HomologicalComplex.homotopyCofiber.fstX S.g (p - 1) p _ = S.f.f p
      rw [HomologicalComplex.homotopyCofiber.inlX_fstX, Category.comp_id]
    · simp only [Category.assoc, HomologicalComplex.comp_f, (hκ p).1,
        comp_zero]
      simp only [Int.reduceNeg, CochainComplex.mappingCocone.lift,
        CochainComplex.mappingCocone.liftCocycle, CochainComplex.mappingCocone.liftCochain,
        CochainComplex.mappingCone.liftCochain,
        CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.mappingCone.inl,
        CochainComplex.mappingCone.inr, CochainComplex.HomComplex.Cochain.zero_comp,
        add_zero, CochainComplex.HomComplex.Cocycle.homOf_f,
        CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
          _ _ _ _ p _ _ (p - 1) (by omega),
        CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
        CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.HomComplex.Cochain.mk_v,
        CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
        Iso.refl_inv, Category.assoc, Iso.refl_hom]
      erw [Category.id_comp, Category.id_comp]
      change S.f.f p ≫ HomologicalComplex.homotopyCofiber.inlX S.g p (p - 1) _ ≫
        HomologicalComplex.homotopyCofiber.sndX S.g (p - 1) = 0
      rw [HomologicalComplex.homotopyCofiber.inlX_sndX, comp_zero]
  rw [heq]
  have := hqκ
  infer_instance

/-- Epimorphic transitions imply that `1 - T` is epic, the first derived limit
vanishes, and the canonical ordinary-to-derived-limit map is an isomorphism.

Source: the Weil conjectures blueprint, main-20261015, `proposition-milnor-sequence`,
`proposition-milnor-sequence--3` (blueprint: proposition-milnor-sequence--3).

Proof:
1. Evaluation at an affine weakly contractible object W preserves cokernels and
zero by proposition-milnor-sequence--3. Thus every epimorphic transition becomes
a surjection of R(W)-modules. Products are computed sectionwise by the same node.
2. Given (a_n), choose right inverses s_n to these surjections. Set m_0 = 0 and
m_(n+1) = s_n(m_n - a_n). Then (1 - T)m = a on W.
3. Apply corollary-evaluation-weakly-contractible-objects to P -> P -> 0, using the preceding
surjectivity, to conclude that 1 - T is an epimorphism of module sheaves.
4. Clause 2 of proposition-milnor-sequence--2 identifies H^0 of its recorded Roos complex
with the ordinary inverse limit (proposition-milnor-sequence--3), H^1 with the
cokernel of 1 - T, and every other H^p with zero. Hence H^1 vanishes.
5. The comparison is the inclusion of this kernel into the two-term Roos complex,
with zero second component. The differential of Cone(1 - T)[-1] is -(1 - T);
negating degree 1 identifies it with the usual two-term complex. The comparison
induces the degree-zero kernel identification and is a quasi-isomorphism. The
localization proposition-milnor-sequence--3 makes it an isomorphism.
The argument uses arbitrary ring sheaves (situation-conventions),
and includes the zero tower and the empty scheme. -/
theorem milnor_epimorphic
    (X : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)]
    (M : ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R)
    (ht : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op)) :
    Epi (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
      (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op)) ∧
      IsZero ((WeilConjectures.integralOperationsRoos
        (Scheme.ProEt.milnorSingleTower M)).homology 1) ∧
      IsIso (DerivedCategory.Q.{w}.map (milnorLimitComparison M)) := by
  have hepi := sheaf_tower_epi X R M ht
  have := hepi
  refine ⟨hepi, ?_, ?_⟩
  · obtain ⟨_, e₁, _⟩ := Scheme.ProEt.milnor_sequence X R
    exact (isZero_cokernel_of_epi _).of_iso (e₁ M)
  · let C := ringedSiteModules.{max u (t + 1)} R
    let E := HomologicalComplex.single C (ComplexShape.up ℤ) 0
    let F := Scheme.ProEt.milnorSingleTower M
    let g := towerTransitionEndomorphism (K := fun n : ℕ ↦ F.obj (op n))
      (WeilConjectures.integralOperationsTowerStep F)
    have hg : Epi g := by
      have : Epi (E.map (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ M.obj (op n))
          (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op))) := inferInstance
      have : Epi (piComparison E (fun n : ℕ ↦ M.obj (op n)) ≫ g) := by
        change Epi (piComparison E (fun n : ℕ ↦ M.obj (op n)) ≫
          towerTransitionEndomorphism (K := fun n : ℕ ↦ E.obj (M.obj (op n)))
            (fun n : ℕ ↦ E.map (M.map (homOfLE (Nat.le_succ n)).op)))
        rw [← map_transition]
        infer_instance
      exact epi_of_epi (piComparison E (fun n : ℕ ↦ M.obj (op n))) g
    have hc : IsLimit (E.mapCone (limit.cone M)) :=
      isLimitOfPreserves E (limit.isLimit M)
    obtain ⟨hz, ⟨hkernel⟩⟩ := tower_kernel F (E.mapCone (limit.cone M)) hc
      (Fan.mk _ (fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj (op n)) n))
      (productIsProduct _) (milnorLimitProjection M) g
      (fun n ↦ by
        change milnorLimitProjection M ≫ Pi.π (fun n : ℕ ↦ F.obj (op n)) n =
          E.map (limit.π M (op n))
        dsimp only [milnorLimitProjection, F, E, C, Scheme.ProEt.milnorSingleTower,
          Functor.comp_obj]
        exact Pi.lift_comp_π _ n)
      (fun n ↦ (towerTransitionEndomorphism_eq_iff _ _).1 rfl n)
    let S := ShortComplex.mk (milnorLimitProjection M) g hz
    have : Mono S.f := mono_of_isLimit_fork hkernel
    have hS : S.ShortExact := { exact := S.exact_of_f_is_kernel hkernel }
    have hq : QuasiIso (milnorLimitComparison M) :=
      cocone_lift_quasiIso S hS (milnorLimitComparison_condition M)
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso C (milnorLimitComparison M)).2 hq

end AlgebraicGeometry.ProEtale
