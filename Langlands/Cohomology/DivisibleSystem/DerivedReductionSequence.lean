import Langlands.Cohomology.RightDerivedAdditive
import Langlands.Cohomology.DivisibleSystem.Colimit
import Langlands.Cohomology.DivisibleSystem.EtaleAdicCohomology
import Langlands.Cohomology.DivisibleSystem.ReductionSequence
import Langlands.Cohomology.RightDerivedSequence

/-!
# Reduction sequences for right derived functors of `ℓ`-divisible systems

Milne, *Étale Cohomology* (1980), Ch. V, §1, Lemma 1.11, printed p.165: for an `l`-adic sheaf
`F = (F_n)` with each `F_n` flat over `ℤ/(l^n)` and all `H^r(X, F_n)` finite, there are exact
sequences `0 → H^r(X_et, F)^(l^n) → H^r(X_et, F_n) → H^{r+1}(X_et, F)_{l^n} → 0`, where
`H^r(X, F) = lim_n H^r(X, F_n)` (p.164). Harris, *Galois properties of cohomological automorphic
forms on GL(n)*, §2, p.304, (2.1), defines `ℓ`-divisible systems (the published
`DivisibleSystem`); the published `harrisEtaleDivisibleSystem` is one of étale sheaves.

The published `ReductionSequence` and `GodementReductionSequence` prove the lemma for systems of
complexes. This module proves it for the right derived functors `R^q F = F.rightDerived q` of an
additive functor `F : C ⥤ D` on an abelian category with enough injectives, and so for étale
cohomology, which is not the cohomology of a functorial system of complexes:

* `powSMulMap`, `powSMulShortComplex_shortExact`: for an `ℓ`-divisible system `T` and
  `m + r = n`, the map `T m ⟶ T n` induced by multiplication by `ℓ ^ r` and the short exact
  sequence `0 ⟶ T m ⟶ T n ⟶ T r ⟶ 0`, natural in `m`;
* `derivedReductionShortComplex_shortExact`: the finite-level sequence
  `0 ⟶ coker R^q F(T m ⟶ T n) ⟶ R^q F(T r) ⟶ ker R^(q+1) F(T m ⟶ T n) ⟶ 0`, from the published
  long exact sequence of right derived functors;
* `derivedAdicReductionSequence`, `derivedAdicReductionSequence_shortExact`: Milne's sequence
  `0 ⟶ (lim_m R^q F(T m)) / ℓ ^ r ⟶ R^q F(T r) ⟶ (lim_m R^(q+1) F(T m))[ℓ ^ r] ⟶ 0`, short exact
  for `R`-modules when every `R^q F(T m)` is finite, given Worker 3's
  `MittagLefflerShortExactLimitStatement` as an explicit hypothesis;
* `etaleReductionSequence`, `harrisEtaleReductionSequence`: the specializations to étale
  cohomology (`EtaleDerivedSections.cohomology`, `EtaleAdicCohomology.adicCohomology`) and to the
  published `harrisEtaleDivisibleSystem`.

The proof follows Milne's: he tensors `0 → ℤ/(l^n) → ℤ/(l^{n+s}) → ℤ/(l^s) → 0` with `F_{n+s}`,
takes cohomology sequences and passes to the inverse limit, using that inverse limits of exact
sequences of finite groups are exact. Here the sequence `0 ⟶ T m ⟶ T (m + r) ⟶ T r ⟶ 0` comes
from the `DivisibleSystem` axioms, and exactness of the limits from Worker 3's statement, which
is not proved here. Only the finiteness of the `R^q F(T m)` in the degree `q` itself is used.
Not formalized: finite generation of `lim_m H^r(X, F_m)` over `ℤ_ℓ`, and any group or Galois
action. The statements and proofs are ours.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u v u' v'



section LevelShift

variable {D : Type u'} [Category.{v'} D]

/-- The functor `ℕ ⥤ ℕ`, `m ↦ m + r`. -/
def levelShift (r : ℕ) : ℕ ⥤ ℕ :=
  Monotone.functor (f := fun m => m + r) fun _ _ h => Nat.add_le_add_right h r

/-- The limit of a constant inverse system is its value (`ℕᵒᵖ` is connected). -/
def constLimitIso (Z : D) : limit ((Functor.const ℕᵒᵖ).obj Z) ≅ Z :=
  limit.isoLimitCone ⟨_, isLimitConstCone ℕᵒᵖ Z⟩

/-- Every limit projection of a constant inverse system is `constLimitIso`. -/
lemma constLimitIso_hom (Z : D) (m : ℕᵒᵖ) :
    (constLimitIso Z).hom = limit.π ((Functor.const ℕᵒᵖ).obj Z) m :=
  (Category.comp_id _).symm.trans (limit.isoLimitCone_hom_π ⟨_, isLimitConstCone ℕᵒᵖ Z⟩ m)

variable [HasLimitsOfShape ℕᵒᵖ D]

/-- `lim_m X(m + r) ≅ lim_m X(m)` for an inverse system `X : ℕᵒᵖ ⥤ D`. Its inverse is
Mathlib's `limit.pre`; its components are the limit projections followed by the transition
maps `X(m + r) ⟶ X(m)`. -/
def levelShiftLimitIso (X : ℕᵒᵖ ⥤ D) (r : ℕ) : limit ((levelShift r).op ⋙ X) ≅ limit X where
  hom := limit.lift X
    { pt := _
      π :=
        { app := fun m => limit.π ((levelShift r).op ⋙ X) m ≫
            X.map (homOfLE (Nat.le_add_right m.unop r)).op
          naturality := fun m m' f => by
            dsimp
            rw [Category.id_comp, ← limit.w ((levelShift r).op ⋙ X) f, Category.assoc,
              Category.assoc]
            exact congrArg (limit.π ((levelShift r).op ⋙ X) m ≫ ·)
              ((X.map_comp ((levelShift r).op.map f)
                (homOfLE (Nat.le_add_right m'.unop r)).op).symm.trans
                (X.map_comp (homOfLE (Nat.le_add_right m.unop r)).op f)) } }
  inv := limit.pre X (levelShift r).op
  hom_inv_id := by
    apply limit.hom_ext
    intro m
    rw [Category.assoc, limit.pre_π, limit.lift_π, Category.id_comp]
    exact limit.w ((levelShift r).op ⋙ X) (homOfLE (Nat.le_add_right m.unop r)).op
  inv_hom_id := by
    apply limit.hom_ext
    intro m
    rw [Category.assoc, limit.lift_π, ← Category.assoc, limit.pre_π, Category.id_comp]
    exact limit.w X _

@[reassoc (attr := simp)]
lemma levelShiftLimitIso_hom_π (X : ℕᵒᵖ ⥤ D) (r : ℕ) (m : ℕᵒᵖ) :
    (levelShiftLimitIso X r).hom ≫ limit.π X m =
      limit.π ((levelShift r).op ⋙ X) m ≫ X.map (homOfLE (Nat.le_add_right m.unop r)).op :=
  limit.lift_π _ _

end LevelShift

section ModuleCatLimit

variable {R : Type u'} [Ring R]

/-- For an exact sequence `X₁ ⟶ X₂ ⟶ X₃` of inverse systems of `R`-modules whose first terms are
finite, the limit sequence `lim X₁ ⟶ lim X₂ ⟶ lim X₃` is exact, given Worker 3's
`MittagLefflerShortExactLimitStatement` (EGA III.0, 13.2.2). Proof: the kernel of
`X₁ ⟶ ker(X₂ ⟶ X₃)` has finite terms, hence is Mittag-Leffler, so `lim X₁ ⟶ lim ker(X₂ ⟶ X₃)`
is surjective, and `lim` preserves kernels. -/
lemma limit_exact_of_finite (hML : MittagLefflerShortExactLimitStatement.{u', v'} R)
    {S : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{v'} R)} (hS : S.Exact)
    (hfin : ∀ m, Finite (S.X₁.obj m)) : (S.map lim).Exact := by
  have : Epi S.toCycles := hS.epi_toCycles
  let S' : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{v'} R) :=
    ShortComplex.mk (kernel.ι S.toCycles) S.toCycles (kernel.condition _)
  have hS' : S'.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
  have hML' : (S'.X₁ ⋙ CategoryTheory.forget (ModuleCat.{v'} R)).IsMittagLeffler := by
    refine Functor.isMittagLeffler_of_exists_finite_range _ fun j => ⟨j, 𝟙 j, ?_⟩
    have := hfin j
    have : Finite ((S'.X₁ ⋙ CategoryTheory.forget (ModuleCat.{v'} R)).obj j) :=
      Finite.of_injective _
        ((ModuleCat.mono_iff_injective ((kernel.ι S.toCycles).app j)).1 inferInstance)
    exact Set.finite_range _
  have : Epi (lim.map S.toCycles) := (hML S' hS' hML').epi_g
  have hk := isLimitForkMapOfIsLimit' lim S.iCycles_g S.cyclesIsKernel
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  have key : kernel.lift (S.map lim).g (S.map lim).f (S.map lim).zero =
      lim.map S.toCycles ≫ (hk.conePointUniqueUpToIso (kernelIsKernel (lim.map S.g))).hom := by
    rw [← cancel_mono (kernel.ι _), kernel.lift_ι, Category.assoc]
    erw [hk.conePointUniqueUpToIso_hom_comp (kernelIsKernel (lim.map S.g))
      WalkingParallelPair.zero]
    exact (congrArg lim.map S.toCycles_i).symm.trans (lim.map_comp _ _)
  rw [key]
  infer_instance

end ModuleCatLimit

namespace DivisibleSystem

section Multiplication

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ} (T : DivisibleSystem C ℓ)

/-- The published short exact sequence `0 ⟶ T r ⟶ T n ⟶ T (n - r) ⟶ 0`, with the third term
written `T k` for any `k = n - r`. -/
lemma shortExact_inclusion_projection {r n : ℕ} (h : r < n) {k : ℕ} (hk : k ≤ n)
    (hk' : n - r = k) :
    (ShortComplex.mk (T.inclusion h) (T.projection hk)
      (by subst hk'; exact T.inclusion_comp h)).ShortExact := by
  subst hk'
  exact T.shortExact h

/-- The published exactness of `T n ⟶ T n ⟶ T n` (multiplication by `ℓ ^ a`, then by
`ℓ ^ b`) for any `n = a + b`. -/
lemma flat_of_add_eq {a b n : ℕ} (h : a + b = n) :
    (ShortComplex.mk (powSMul ℓ a (T.obj n)) (powSMul ℓ b (T.obj n))
      (by rw [powSMul_comp_powSMul, h, T.powSMul_eq_zero])).Exact := by
  subst h
  exact T.flat a b

/-- Multiplication by `ℓ ^ r` on `T n` vanishes on the kernel of the projection
`T n ⟶ T m`, `m + r = n`. -/
lemma kernel_ι_projection_comp_powSMul {m r n : ℕ} (h : m + r = n) (hmn : m ≤ n) :
    kernel.ι (T.projection hmn) ≫ powSMul ℓ r (T.obj n) = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain rfl : r = n := by omega
    rw [T.powSMul_eq_zero, comp_zero]
  · have hS := T.shortExact_inclusion_projection (show r < n by omega) hmn (by omega)
    rw [← hS.exact.lift_f (kernel.ι _) (kernel.condition _), Category.assoc]
    change _ ≫ T.inclusion _ ≫ _ = 0
    rw [comp_powSMul, T.powSMul_eq_zero, zero_comp, comp_zero]

/-- The map `T m ⟶ T n`, `m + r = n`, induced by multiplication by `ℓ ^ r` on `T n`: the
projection `T n ⟶ T m` followed by it is multiplication by `ℓ ^ r`
(`projection_comp_powSMulMap`). For `T m = Λ / ℓ ^ m` it is `x ↦ ℓ ^ r x`. -/
def powSMulMap {m r n : ℕ} (h : m + r = n) : T.obj m ⟶ T.obj n :=
  haveI := T.epi_projection (show m ≤ n by omega)
  Abelian.epiDesc (T.projection (show m ≤ n by omega)) (powSMul ℓ r (T.obj n))
    (T.kernel_ι_projection_comp_powSMul h _)

/-- The projection `T n ⟶ T m` followed by `powSMulMap` is multiplication by `ℓ ^ r`. -/
@[reassoc (attr := simp)]
lemma projection_comp_powSMulMap {m r n : ℕ} (h : m + r = n) (hmn : m ≤ n) :
    T.projection hmn ≫ T.powSMulMap h = powSMul ℓ r (T.obj n) :=
  have := T.epi_projection hmn
  Abelian.comp_epiDesc _ _ _

/-- `powSMulMap` followed by the projection `T n ⟶ T m` is multiplication by `ℓ ^ r`. -/
@[reassoc (attr := simp)]
lemma powSMulMap_comp_projection {m r n : ℕ} (h : m + r = n) (hmn : m ≤ n) :
    T.powSMulMap h ≫ T.projection hmn = powSMul ℓ r (T.obj m) := by
  have := T.epi_projection hmn
  rw [← cancel_epi (T.projection hmn), projection_comp_powSMulMap_assoc, ← comp_powSMul]

/-- `powSMulMap` is natural in `m` for fixed `r`. -/
@[reassoc]
lemma projection_comp_powSMulMap_comm {m r n m' n' : ℕ} (h : m + r = n) (h' : m' + r = n')
    (hm : m' ≤ m) (hn : n' ≤ n) :
    T.projection hm ≫ T.powSMulMap h' = T.powSMulMap h ≫ T.projection hn := by
  have := T.epi_projection (show m ≤ n by omega)
  rw [← cancel_epi (T.projection (show m ≤ n by omega)), projection_comp_powSMulMap_assoc,
    ← comp_powSMul, ← T.projection_comp_powSMulMap h' (show m' ≤ n' by omega)]
  simp only [← Category.assoc, ← Functor.map_comp]
  rfl

/-- `powSMulMap` is a monomorphism: the projection `T n ⟶ T m` is a cokernel of
`i : T r ⟶ T n`, which is a kernel of multiplication by `ℓ ^ r`. -/
instance mono_powSMulMap {m r n : ℕ} (h : m + r = n) : Mono (T.powSMulMap h) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨fun _ _ _ => T.isZero_obj_zero.eq_of_tgt _ _⟩
  have hr : r < n := by omega
  have hmn : m ≤ n := by omega
  have hc := (T.shortExact_inclusion_projection hr hmn (by omega)).gIsCokernel
  have hz : T.inclusion hr ≫ powSMul ℓ r (T.obj n) = 0 := by
    rw [comp_powSMul, T.powSMul_eq_zero, zero_comp]
  have hmono : Mono (cokernel.desc (T.inclusion hr) (powSMul ℓ r (T.obj n)) hz) :=
    (ShortComplex.exact_iff_mono_cokernel_desc _).1 (T.torsion_exact hr)
  have := T.epi_projection hmn
  have key : T.powSMulMap h = (hc.coconePointUniqueUpToIso
      (cokernelIsCokernel (T.inclusion hr))).hom ≫
      cokernel.desc (T.inclusion hr) (powSMul ℓ r (T.obj n)) hz := by
    rw [← cancel_epi (T.projection hmn), projection_comp_powSMulMap]
    have := hc.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel (T.inclusion hr))
      WalkingParallelPair.one
    dsimp at this
    rw [reassoc_of% this, cokernel.π_desc]
  rw [key]
  infer_instance

/-- The short complex `T m ⟶ T n ⟶ T r`, `m + r = n`: multiplication by `ℓ ^ r`
(`powSMulMap`), then the projection. -/
@[simps]
def powSMulShortComplex {m r n : ℕ} (h : m + r = n) : ShortComplex C :=
  ShortComplex.mk (T.powSMulMap h) (T.projection (show r ≤ n by omega)) (by
    have := T.epi_projection (show m ≤ n by omega)
    rw [← cancel_epi (T.projection (show m ≤ n by omega)), projection_comp_powSMulMap_assoc,
      ← comp_powSMul, T.powSMul_eq_zero, comp_zero, comp_zero])

/-- `0 ⟶ T m ⟶ T n ⟶ T r ⟶ 0` is short exact. Proof: after precomposing with the epimorphism
`T n ⟶ T m` and postcomposing with the monomorphism `powSMulMap : T r ⟶ T n`, the sequence
becomes the published exact sequence `T n ⟶ T n ⟶ T n` of multiplications by `ℓ ^ r` and
`ℓ ^ m`. -/
lemma powSMulShortComplex_shortExact {m r n : ℕ} (h : m + r = n) :
    (T.powSMulShortComplex h).ShortExact := by
  have hmn : m ≤ n := by omega
  have hrn : r ≤ n := by omega
  let S : ShortComplex C := ShortComplex.mk (powSMul ℓ r (T.obj n)) (T.projection hrn) (by
    rw [← comp_powSMul, T.powSMul_eq_zero, comp_zero])
  let S' : ShortComplex C := ShortComplex.mk (powSMul ℓ r (T.obj n)) (powSMul ℓ m (T.obj n))
    (by rw [powSMul_comp_powSMul, show r + m = n by omega, T.powSMul_eq_zero])
  let φ₁ : S ⟶ T.powSMulShortComplex h :=
    { τ₁ := T.projection hmn
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        change T.projection hmn ≫ T.powSMulMap h = powSMul ℓ r (T.obj n) ≫ 𝟙 _
        rw [Category.comp_id]
        exact T.projection_comp_powSMulMap h hmn
      comm₂₃ := by
        change 𝟙 _ ≫ T.projection hrn = T.projection hrn ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id] }
  let φ₂ : S ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := T.powSMulMap (show r + m = n by omega)
      comm₁₂ := by
        change 𝟙 _ ≫ powSMul ℓ r (T.obj n) = powSMul ℓ r (T.obj n) ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]
      comm₂₃ := by
        change 𝟙 _ ≫ powSMul ℓ m (T.obj n) = T.projection hrn ≫ T.powSMulMap _
        rw [Category.id_comp]
        exact (T.projection_comp_powSMulMap (show r + m = n by omega) hrn).symm }
  have : Epi φ₁.τ₁ := T.epi_projection hmn
  have : IsIso φ₁.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ₁.τ₃ := inferInstanceAs (Mono (𝟙 _))
  have : Epi φ₂.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso φ₂.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ₂.τ₃ := T.mono_powSMulMap (show r + m = n by omega)
  have : Mono (T.powSMulShortComplex h).f := T.mono_powSMulMap h
  have : Epi (T.powSMulShortComplex h).g := T.epi_projection hrn
  exact ⟨(ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₁).1
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₂).2
      (T.flat_of_add_eq (show r + m = n by omega)))⟩

/-- For `m' ≤ m`, the projections give a morphism from the sequence
`T m ⟶ T n ⟶ T r` to `T m' ⟶ T n' ⟶ T r` that is the identity on `T r`. -/
@[simps]
def powSMulShortComplexMap {m r n m' n' : ℕ} (h : m + r = n) (h' : m' + r = n') (hm : m' ≤ m)
    (hn : n' ≤ n) : T.powSMulShortComplex h ⟶ T.powSMulShortComplex h' where
  τ₁ := T.projection hm
  τ₂ := T.projection hn
  τ₃ := 𝟙 _
  comm₁₂ := T.projection_comp_powSMulMap_comm h h' hm hn
  comm₂₃ := by
    change T.projection hn ≫ T.projection _ = T.projection _ ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp]
    rfl

end Multiplication


section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (F : C ⥤ D) [F.Additive] {ℓ : ℕ} (T : DivisibleSystem C ℓ)

/-- The connecting map `R^q F(T r) ⟶ R^(q+1) F(T m)` of the long exact sequence of
`0 ⟶ T m ⟶ T n ⟶ T r ⟶ 0` (`powSMulShortComplex`), `m + r = n`. -/
def derivedReductionδ {m r n : ℕ} (h : m + r = n) (q : ℕ) :
    (F.rightDerived q).obj (T.obj r) ⟶ (F.rightDerived (q + 1)).obj (T.obj m) :=
  DerivedPlus.rightDerivedδ F (T.powSMulShortComplex_shortExact h) q (q + 1) rfl

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- `R^q F(T m) ⟶ R^q F(T n) ⟶ R^q F(T r)` composes to zero. -/
@[reassoc (attr := simp)]
lemma map_powSMulMap_comp_map_projection {m r n : ℕ} (h : m + r = n) (hrn : r ≤ n) (q : ℕ) :
    (F.rightDerived q).map (T.powSMulMap h) ≫ (F.rightDerived q).map (T.projection hrn) = 0 :=
  DerivedPlus.rightDerived_map_comp_map F (S := T.powSMulShortComplex h) q

/-- `R^q F(T n) ⟶ R^q F(T r) ⟶ R^(q+1) F(T m)` composes to zero. -/
@[reassoc (attr := simp)]
lemma map_projection_comp_derivedReductionδ {m r n : ℕ} (h : m + r = n) (hrn : r ≤ n)
    (q : ℕ) :
    (F.rightDerived q).map (T.projection hrn) ≫ T.derivedReductionδ F h q = 0 :=
  DerivedPlus.rightDerived_map_comp_δ F (T.powSMulShortComplex_shortExact h) q (q + 1) rfl

/-- `R^q F(T r) ⟶ R^(q+1) F(T m) ⟶ R^(q+1) F(T n)` composes to zero. -/
@[reassoc (attr := simp)]
lemma derivedReductionδ_comp_map_powSMulMap {m r n : ℕ} (h : m + r = n) (q : ℕ) :
    T.derivedReductionδ F h q ≫ (F.rightDerived (q + 1)).map (T.powSMulMap h) = 0 :=
  DerivedPlus.rightDerivedδ_comp_map F (T.powSMulShortComplex_shortExact h) q (q + 1) rfl

/-- The connecting maps are compatible with the projections `T m ⟶ T m'`. -/
@[reassoc]
lemma derivedReductionδ_comp_map_projection {m r n m' n' : ℕ} (h : m + r = n)
    (h' : m' + r = n') (hm : m' ≤ m) (q : ℕ) :
    T.derivedReductionδ F h q ≫ (F.rightDerived (q + 1)).map (T.projection hm) =
      T.derivedReductionδ F h' q := by
  have := DerivedPlus.rightDerivedδ_naturality F (T.powSMulShortComplex_shortExact h)
    (T.powSMulShortComplex_shortExact h') (T.powSMulShortComplexMap h h' hm (by omega)) q (q + 1)
    rfl
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at this
  exact this

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- `R^q F(T m) ⟶ R^q F(T m) ⟶ R^q F(T n)`, the map induced by `powSMulMap` followed by the
one induced by the projection `T n ⟶ T m`, is multiplication by `ℓ ^ r`. -/
lemma map_powSMulMap_comp_map_projection_eq {m r n : ℕ} (h : m + r = n) (hmn : m ≤ n)
    (q : ℕ) :
    (F.rightDerived q).map (T.powSMulMap h) ≫ (F.rightDerived q).map (T.projection hmn) =
      powSMul ℓ r ((F.rightDerived q).obj (T.obj m)) := by
  rw [← Functor.map_comp, powSMulMap_comp_projection, map_powSMul]

/-- The finite-level reduction sequence
`coker R^q F(T m ⟶ T n) ⟶ R^q F(T r) ⟶ ker R^(q+1) F(T m ⟶ T n)`, `m + r = n`, the maps
`T m ⟶ T n` being `powSMulMap`. -/
def derivedReductionShortComplex {m r n : ℕ} (h : m + r = n) (q : ℕ) : ShortComplex D :=
  cokernelKernelShortComplex ((F.rightDerived q).map (T.powSMulMap h))
    ((F.rightDerived q).map (T.projection (show r ≤ n by omega))) (T.derivedReductionδ F h q)
    ((F.rightDerived (q + 1)).map (T.powSMulMap h))
    (T.map_powSMulMap_comp_map_projection F h _ q)
    (T.map_projection_comp_derivedReductionδ F h _ q)
    (T.derivedReductionδ_comp_map_powSMulMap F h q)

/-- The finite-level reduction sequence is short exact: the long exact sequence of right
derived functors of `0 ⟶ T m ⟶ T n ⟶ T r ⟶ 0` is exact at its three middle terms. -/
lemma derivedReductionShortComplex_shortExact {m r n : ℕ} (h : m + r = n) (q : ℕ) :
    (T.derivedReductionShortComplex F h q).ShortExact :=
  cokernelKernelShortComplex_shortExact
    (DerivedPlus.rightDerived_exact₂ F (T.powSMulShortComplex_shortExact h) q)
    (DerivedPlus.rightDerived_exact₃ F (T.powSMulShortComplex_shortExact h) q (q + 1) rfl)
    (DerivedPlus.rightDerived_exact₁ F (T.powSMulShortComplex_shortExact h) q (q + 1) rfl)

end Derived


section DerivedLimit

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  [HasLimitsOfShape ℕᵒᵖ D]
variable (F : C ⥤ D) [F.Additive] {ℓ : ℕ} (T : DivisibleSystem C ℓ)

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasLimitsOfShape ℕᵒᵖ D] in
/-- The maps `R^q F(T m) ⟶ R^q F(T (m + r))` induced by `powSMulMap`, as a morphism of
inverse systems. -/
@[simps]
def derivedPowSMulNatTrans (r q : ℕ) :
    T.tower ⋙ F.rightDerived q ⟶ (levelShift r).op ⋙ T.tower ⋙ F.rightDerived q where
  app m := (F.rightDerived q).map (T.powSMulMap (m := m.unop) rfl)
  naturality _ _ f :=
    ((F.rightDerived q).map_comp _ _).symm.trans
      ((congrArg (F.rightDerived q).map (T.projection_comp_powSMulMap_comm rfl rfl
        (leOfHom f.unop) (Nat.add_le_add_right (leOfHom f.unop) r))).trans
        ((F.rightDerived q).map_comp _ _))

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasLimitsOfShape ℕᵒᵖ D] in
/-- The maps `R^q F(T (m + r)) ⟶ R^q F(T r)` induced by the projections, as a morphism to the
constant inverse system. -/
@[simps]
def derivedReductionNatTrans (r q : ℕ) :
    (levelShift r).op ⋙ T.tower ⋙ F.rightDerived q ⟶
      (Functor.const ℕᵒᵖ).obj ((F.rightDerived q).obj (T.obj r)) where
  app m := (F.rightDerived q).map (T.projection (Nat.le_add_left r m.unop))
  naturality _ _ _ :=
    ((F.rightDerived q).map_comp _ _).symm.trans
      ((congrArg (F.rightDerived q).map (T.tower.map_comp _ _).symm).trans
        (Category.comp_id _).symm)

omit [HasLimitsOfShape ℕᵒᵖ D] in
/-- The connecting maps `R^q F(T r) ⟶ R^(q+1) F(T m)`, as a morphism from the constant inverse
system. -/
@[simps]
def derivedReductionδNatTrans (r q : ℕ) :
    (Functor.const ℕᵒᵖ).obj ((F.rightDerived q).obj (T.obj r)) ⟶
      T.tower ⋙ F.rightDerived (q + 1) where
  app m := T.derivedReductionδ F (m := m.unop) rfl q
  naturality _ _ f :=
    (Category.id_comp _).trans
      (T.derivedReductionδ_comp_map_projection F rfl rfl (leOfHom f.unop) q).symm

/-- `R^q F(T r) ⟶ lim_m R^(q+1) F(T m)`, induced by the connecting maps. -/
def derivedAdicδ (r q : ℕ) :
    (F.rightDerived q).obj (T.obj r) ⟶ limit (T.tower ⋙ F.rightDerived (q + 1)) :=
  limit.lift _ ⟨_, T.derivedReductionδNatTrans F r q⟩

/-- The components of `derivedAdicδ` are the connecting maps `derivedReductionδ`. -/
@[reassoc (attr := simp)]
lemma derivedAdicδ_π (r q m : ℕ) :
    T.derivedAdicδ F r q ≫ limit.π (T.tower ⋙ F.rightDerived (q + 1)) (op m) =
      T.derivedReductionδ F (m := m) rfl q :=
  limit.lift_π _ _

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- Multiplication by `ℓ ^ r` on `lim_m R^q F(T m)` followed by the projection to
`R^q F(T r)` is zero, since `ℓ ^ r` kills `T r`. -/
lemma powSMul_limit_comp_π_eq_zero (r q : ℕ) :
    powSMul ℓ r (limit (T.tower ⋙ F.rightDerived q)) ≫
      limit.π (T.tower ⋙ F.rightDerived q) (op r) = 0 := by
  rw [← comp_powSMul]
  have : powSMul ℓ r ((T.tower ⋙ F.rightDerived q).obj (op r)) = 0 := by
    change powSMul ℓ r ((F.rightDerived q).obj (T.obj r)) = 0
    rw [← map_powSMul, T.powSMul_eq_zero, Functor.map_zero]
  rw [this, comp_zero]

/-- The projection to `R^q F(T r)` followed by `derivedAdicδ` is zero: it factors through
`R^q F(T (m + r)) ⟶ R^q F(T r)`, which the connecting map kills. -/
lemma π_comp_derivedAdicδ (r q : ℕ) :
    limit.π (T.tower ⋙ F.rightDerived q) (op r) ≫ T.derivedAdicδ F r q = 0 := by
  apply limit.hom_ext
  rintro ⟨m⟩
  rw [Category.assoc, derivedAdicδ_π, zero_comp,
    ← limit.w (T.tower ⋙ F.rightDerived q) (homOfLE (Nat.le_add_left r m)).op, Category.assoc,
    Functor.comp_map, map_projection_comp_derivedReductionδ, comp_zero]

/-- `derivedAdicδ` followed by multiplication by `ℓ ^ r` is zero: in level `m`,
multiplication by `ℓ ^ r` on `R^(q+1) F(T m)` factors through `R^(q+1) F(powSMulMap)`. -/
lemma derivedAdicδ_comp_powSMul (r q : ℕ) :
    T.derivedAdicδ F r q ≫ powSMul ℓ r (limit (T.tower ⋙ F.rightDerived (q + 1))) = 0 := by
  apply limit.hom_ext
  rintro ⟨m⟩
  rw [Category.assoc, ← comp_powSMul, derivedAdicδ_π_assoc, zero_comp]
  change T.derivedReductionδ F rfl q ≫ powSMul ℓ r ((F.rightDerived (q + 1)).obj (T.obj m)) = 0
  rw [← T.map_powSMulMap_comp_map_projection_eq F (rfl : m + r = m + r) (Nat.le_add_right m r),
    derivedReductionδ_comp_map_powSMulMap_assoc, zero_comp]

/-- Milne, Ch. V, Lemma 1.11, for right derived functors: the short complex
`(lim_m R^q F(T m)) / ℓ ^ r ⟶ R^q F(T r) ⟶ (lim_m R^(q+1) F(T m))[ℓ ^ r]` whose first map is
induced by the limit projection and whose second map is induced by `derivedAdicδ`. -/
def derivedAdicReductionSequence (r q : ℕ) : ShortComplex D :=
  cokernelKernelShortComplex (powSMul ℓ r (limit (T.tower ⋙ F.rightDerived q)))
    (limit.π (T.tower ⋙ F.rightDerived q) (op r)) (T.derivedAdicδ F r q)
    (powSMul ℓ r (limit (T.tower ⋙ F.rightDerived (q + 1))))
    (T.powSMul_limit_comp_π_eq_zero F r q) (T.π_comp_derivedAdicδ F r q)
    (T.derivedAdicδ_comp_powSMul F r q)

/-- The first map of `derivedAdicReductionSequence` after the projection to the cokernel is the
limit projection to `R^q F(T r)`. -/
@[reassoc (attr := simp)]
lemma reductionπ_derivedAdicReductionSequence_f (r q : ℕ) :
    reductionπ ℓ (limit (T.tower ⋙ F.rightDerived q)) r ≫
        (T.derivedAdicReductionSequence F r q).f =
      limit.π (T.tower ⋙ F.rightDerived q) (op r) :=
  cokernel.π_desc _ _ _

/-- The second map of `derivedAdicReductionSequence` followed by the inclusion of the
`ℓ ^ r`-torsion is `derivedAdicδ`. -/
@[reassoc (attr := simp)]
lemma derivedAdicReductionSequence_g_ι (r q : ℕ) :
    (T.derivedAdicReductionSequence F r q).g ≫
        kernel.ι (powSMul ℓ r (limit (T.tower ⋙ F.rightDerived (q + 1)))) =
      T.derivedAdicδ F r q :=
  kernel.lift_ι _ _ _

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- Under `levelShiftLimitIso`, the limit of the maps `R^q F(powSMulMap)` is multiplication by
`ℓ ^ r` on `lim_m R^q F(T m)`. -/
lemma limMap_derivedPowSMulNatTrans_comp_levelShiftLimitIso (r q : ℕ) :
    limMap (T.derivedPowSMulNatTrans F r q) ≫
        (levelShiftLimitIso (T.tower ⋙ F.rightDerived q) r).hom =
      powSMul ℓ r (limit (T.tower ⋙ F.rightDerived q)) := by
  apply limit.hom_ext
  rintro ⟨m⟩
  rw [Category.assoc, levelShiftLimitIso_hom_π, limMap_π_assoc, ← comp_powSMul]
  exact congrArg (limit.π (T.tower ⋙ F.rightDerived q) (op m) ≫ ·)
    (T.map_powSMulMap_comp_map_projection_eq F (rfl : m + r = m + r) (Nat.le_add_right m r) q)

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- Under `levelShiftLimitIso` and `constLimitIso`, the limit of the maps
`R^q F(T (m + r)) ⟶ R^q F(T r)` is the limit projection to `R^q F(T r)`. -/
lemma limMap_derivedReductionNatTrans_comp_constLimitIso (r q : ℕ) :
    limMap (T.derivedReductionNatTrans F r q) ≫ (constLimitIso _).hom =
      (levelShiftLimitIso (T.tower ⋙ F.rightDerived q) r).hom ≫
        limit.π (T.tower ⋙ F.rightDerived q) (op r) := by
  rw [constLimitIso_hom _ (op r), limMap_π, levelShiftLimitIso_hom_π]
  rfl

/-- Under `constLimitIso`, the limit of the connecting maps is `derivedAdicδ`. -/
lemma limMap_derivedReductionδNatTrans (r q : ℕ) :
    limMap (T.derivedReductionδNatTrans F r q) = (constLimitIso _).hom ≫ T.derivedAdicδ F r q := by
  apply limit.hom_ext
  rintro ⟨m⟩
  rw [limMap_π, Category.assoc, derivedAdicδ_π, constLimitIso_hom _ (op m)]
  rfl

end DerivedLimit

section ModuleCat

variable {R : Type u'} [Ring R]


variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C] [HasDerivedCategory.{w'} (ModuleCat.{v'} R)]
variable (F : C ⥤ ModuleCat.{v'} R) [F.Additive] {ℓ : ℕ} (T : DivisibleSystem C ℓ)

/-- Milne, Ch. V, Lemma 1.11, for right derived functors with values in `R`-modules: if every
`R^q F(T m)` is finite, then
`0 ⟶ (lim_m R^q F(T m)) / ℓ ^ r ⟶ R^q F(T r) ⟶ (lim_m R^(q+1) F(T m))[ℓ ^ r] ⟶ 0` is short
exact, given Worker 3's `MittagLefflerShortExactLimitStatement`. Proof: the exact sequences
of inverse systems `R^q F(T m) ⟶ R^q F(T (m + r)) ⟶ R^q F(T r) ⟶ R^(q+1) F(T m) ⟶
R^(q+1) F(T (m + r))` (the middle one constant) remain exact in the limit
(`limit_exact_of_finite`); identifying `lim_m R^q F(T (m + r))` with `lim_m R^q F(T m)`
turns the limit of `R^q F(powSMulMap)` into multiplication by `ℓ ^ r`. -/
theorem derivedAdicReductionSequence_shortExact
    (hML : MittagLefflerShortExactLimitStatement.{u', v'} R) (r q : ℕ)
    (hfin : ∀ m, Finite ((F.rightDerived q).obj (T.obj m))) :
    (T.derivedAdicReductionSequence F r q).ShortExact := by
  let E₁ : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{v'} R) :=
    ShortComplex.mk (T.derivedPowSMulNatTrans F r q) (T.derivedReductionNatTrans F r q) (by
      refine NatTrans.ext (funext fun m => ?_)
      rw [NatTrans.comp_app, NatTrans.app_zero]
      exact T.map_powSMulMap_comp_map_projection F rfl _ q)
  let E₂ : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{v'} R) :=
    ShortComplex.mk (T.derivedReductionNatTrans F r q) (T.derivedReductionδNatTrans F r q) (by
      refine NatTrans.ext (funext fun m => ?_)
      rw [NatTrans.comp_app, NatTrans.app_zero]
      exact T.map_projection_comp_derivedReductionδ F rfl _ q)
  let E₃ : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{v'} R) :=
    ShortComplex.mk (T.derivedReductionδNatTrans F r q) (T.derivedPowSMulNatTrans F r (q + 1))
      (by
        refine NatTrans.ext (funext fun m => ?_)
        rw [NatTrans.comp_app, NatTrans.app_zero]
        exact T.derivedReductionδ_comp_map_powSMulMap F rfl q)
  have h₁ : (E₁.map lim).Exact := limit_exact_of_finite hML
    (shortComplex_exact_of_evaluation fun m =>
      DerivedPlus.rightDerived_exact₂ F (T.powSMulShortComplex_shortExact (m := m.unop) rfl) q)
    fun m => hfin m.unop
  have h₂ : (E₂.map lim).Exact := limit_exact_of_finite hML
    (shortComplex_exact_of_evaluation fun m =>
      DerivedPlus.rightDerived_exact₃ F (T.powSMulShortComplex_shortExact (m := m.unop) rfl) q
        (q + 1) rfl)
    fun m => hfin (m.unop + r)
  have h₃ : (E₃.map lim).Exact := limit_exact_of_finite hML
    (shortComplex_exact_of_evaluation fun m =>
      DerivedPlus.rightDerived_exact₁ F (T.powSMulShortComplex_shortExact (m := m.unop) rfl) q
        (q + 1) rfl)
    fun _ => hfin r
  have p₁ : (ShortComplex.mk _ _ (T.powSMul_limit_comp_π_eq_zero F r q)).Exact :=
    ShortComplex.exact_of_iso (ShortComplex.isoMk (S₁ := E₁.map lim) (Iso.refl _)
      (levelShiftLimitIso (T.tower ⋙ F.rightDerived q) r) (constLimitIso _)
      ((T.limMap_derivedPowSMulNatTrans_comp_levelShiftLimitIso F r q).trans
        (Category.id_comp _).symm).symm
      (T.limMap_derivedReductionNatTrans_comp_constLimitIso F r q).symm) h₁
  have p₂ : (ShortComplex.mk _ _ (T.π_comp_derivedAdicδ F r q)).Exact :=
    ShortComplex.exact_of_iso (ShortComplex.isoMk (S₁ := E₂.map lim)
      (levelShiftLimitIso (T.tower ⋙ F.rightDerived q) r) (constLimitIso _) (Iso.refl _)
      (T.limMap_derivedReductionNatTrans_comp_constLimitIso F r q).symm
      ((Category.comp_id _).trans (T.limMap_derivedReductionδNatTrans F r q)).symm) h₂
  have p₃ : (ShortComplex.mk _ _ (T.derivedAdicδ_comp_powSMul F r q)).Exact :=
    ShortComplex.exact_of_iso (ShortComplex.isoMk (S₁ := E₃.map lim) (constLimitIso _)
      (Iso.refl _)
      (levelShiftLimitIso (T.tower ⋙ F.rightDerived (q + 1)) r)
      ((Category.comp_id _).trans (T.limMap_derivedReductionδNatTrans F r q)).symm
      ((T.limMap_derivedPowSMulNatTrans_comp_levelShiftLimitIso F r (q + 1)).trans
        (Category.id_comp _).symm).symm) h₃
  exact cokernelKernelShortComplex_shortExact p₁ p₂ p₃

end ModuleCat

section Etale

open _root_.AlgebraicGeometry Langlands.Geometry

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
  [HasDerivedCategory.{w} (EtaleDerivedSections.ModuleSheaf X R)]
  [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
variable {ℓ : ℕ} (T : DivisibleSystem (EtaleDerivedSections.ModuleSheaf X R) ℓ)

/-- Milne, Ch. V, Lemma 1.11, for étale cohomology: for an `ℓ`-divisible system `T` of étale
sheaves of `R`-modules on `X`, the short complex
`(lim_m H^q(X, T m)) / ℓ ^ r ⟶ H^q(X, T r) ⟶ (lim_m H^(q+1)(X, T m))[ℓ ^ r]`
(`derivedAdicReductionSequence` for the global sections functor). -/
def etaleReductionSequence (r q : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  T.derivedAdicReductionSequence (EtaleDerivedSections.sections X R) r q

/-- The first term is the reduction modulo `ℓ ^ r` of the published
`EtaleAdicCohomology.adicCohomology X R q` of the inverse system of `T`. -/
lemma etaleReductionSequence_X₁ (r q : ℕ) :
    (etaleReductionSequence X R T r q).X₁ =
      cokernel (powSMul ℓ r ((EtaleAdicCohomology.adicCohomology X R q).obj T.tower)) :=
  rfl

/-- The middle term is the published `EtaleDerivedSections.cohomology X R q` of `T r`. -/
lemma etaleReductionSequence_X₂ (r q : ℕ) :
    (etaleReductionSequence X R T r q).X₂ = (EtaleDerivedSections.cohomology X R q).obj (T.obj r) :=
  rfl

/-- The third term is the `ℓ ^ r`-torsion of `EtaleAdicCohomology.adicCohomology X R (q + 1)`
of the inverse system of `T`. -/
lemma etaleReductionSequence_X₃ (r q : ℕ) :
    (etaleReductionSequence X R T r q).X₃ =
      kernel (powSMul ℓ r ((EtaleAdicCohomology.adicCohomology X R (q + 1)).obj T.tower)) :=
  rfl

/-- If every `H^q(X, T m)` is finite, then
`0 ⟶ (lim_m H^q(X, T m)) / ℓ ^ r ⟶ H^q(X, T r) ⟶ (lim_m H^(q+1)(X, T m))[ℓ ^ r] ⟶ 0` is short
exact, given Worker 3's `MittagLefflerShortExactLimitStatement`. -/
theorem etaleReductionSequence_shortExact (hML : MittagLefflerShortExactLimitStatement.{u, u} R)
    (r q : ℕ) (hfin : ∀ m, Finite ((EtaleDerivedSections.cohomology X R q).obj (T.obj m))) :
    (etaleReductionSequence X R T r q).ShortExact :=
  T.derivedAdicReductionSequence_shortExact _ hML r q hfin

end Etale

section Harris

open _root_.AlgebraicGeometry Langlands.Geometry Langlands.Global Langlands.Shimura
  Langlands.Shimura.Coefficients

variable (ℓ : ℕ) [NeZero ℓ]
variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints)
variable (X : Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U ℓ) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n))
variable [HasDerivedCategory.{w}
    (EtaleDerivedSections.ModuleSheaf X (HarrisCoefficientIntegers L p))]
  [HasDerivedCategory.{w'} (ModuleCat.{u} (HarrisCoefficientIntegers L p))]

/-- Harris's reduction sequence for the published étale `ℓ`-divisible system
`harrisEtaleDivisibleSystem` of the sheaves `𝓛 / ℓ ^ m`:
`(lim_m H^q(X, 𝓛 / ℓ ^ m)) / ℓ ^ r ⟶ H^q(X, 𝓛 / ℓ ^ r) ⟶ (lim_m H^(q+1)(X, 𝓛 / ℓ ^ m))[ℓ ^ r]`. -/
def harrisEtaleReductionSequence (r q : ℕ) :
    ShortComplex (ModuleCat.{u} (HarrisCoefficientIntegers L p)) :=
  etaleReductionSequence X _ (harrisEtaleDivisibleSystem ℓ ρ p U X Y hY) r q

/-- The first term is the reduction modulo `ℓ ^ r` of the published
`harrisEtaleAdicCohomology` in degree `q`. -/
lemma harrisEtaleReductionSequence_X₁ (r q : ℕ) :
    (harrisEtaleReductionSequence ℓ ρ p U X Y hY r q).X₁ =
      cokernel (powSMul ℓ r (EtaleAdicCohomology.harrisEtaleAdicCohomology ℓ ρ p U X Y hY q)) :=
  rfl

/-- The third term is the `ℓ ^ r`-torsion of the published `harrisEtaleAdicCohomology` in
degree `q + 1`. -/
lemma harrisEtaleReductionSequence_X₃ (r q : ℕ) :
    (harrisEtaleReductionSequence ℓ ρ p U X Y hY r q).X₃ =
      kernel (powSMul ℓ r
        (EtaleAdicCohomology.harrisEtaleAdicCohomology ℓ ρ p U X Y hY (q + 1))) :=
  rfl

/-- If every `H^q(X, 𝓛 / ℓ ^ m)` is finite, Harris's reduction sequence is short exact, given
Worker 3's `MittagLefflerShortExactLimitStatement`. -/
theorem harrisEtaleReductionSequence_shortExact
    (hML : MittagLefflerShortExactLimitStatement.{u, u} (HarrisCoefficientIntegers L p))
    (r q : ℕ)
    (hfin : ∀ m, Finite ((EtaleDerivedSections.cohomology X (HarrisCoefficientIntegers L p) q).obj
      ((harrisEtaleDivisibleSystem ℓ ρ p U X Y hY).obj m))) :
    (harrisEtaleReductionSequence ℓ ρ p U X Y hY r q).ShortExact :=
  etaleReductionSequence_shortExact X _ _ hML r q hfin

end Harris

end DivisibleSystem

end Langlands.Cohomology
