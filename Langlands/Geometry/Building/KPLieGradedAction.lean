import Langlands.Geometry.Building.KPLieFiltrationDual
import Langlands.GroupScheme.IntegralModel.LieLatticeAdjoint

/-!
# The adjoint action on the graded pieces `𝔤_{x,r}/𝔤_{x,r+}` and `𝔤*_{x,r}/𝔤*_{x,r+}`

For supplied `L : P.LieFiltrationData`, this module defines the subgroup of `G(F)` whose adjoint
action stabilizes the lattices `𝔤_{x,r}`, shows that it then stabilizes the real-depth lattices
and the dual lattices of KP 13.3.1, and defines the induced representations on the graded pieces
of KP 13.3.4, together with their factorization through a quotient of the parahoric subgroup.
It also gives a criterion (left continuity of the filtration at `-r`) under which a subgroup
acting trivially on `𝔤_{x,-r}/𝔤_{x,(-r)+}` acts trivially on `𝔤*_{x,r}/𝔤*_{x,r+}`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData

variable {F : Type u} [Field F] [ValuativeRel F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-! ### The `F`-linear adjoint action -/

/-- The adjoint action of `g ∈ G(F)` on `𝔤 = GenericLie 𝒪[F] G` as an `F`-linear map. Its
underlying map is that of `GenericLie.adjoint 𝒪[F] g`; `adjointF_apply` states this pointwise
and holds by `rfl`. -/
def adjointF (g : rationalPoints G) : GenericLie 𝒪[F] G →ₗ[F] GenericLie 𝒪[F] G :=
  ((GenericLie.equiv 𝒪[F] G).symm.toLinearMap.comp
      (GroupScheme.adjoint G F (AffineWeil.sectionsCoeffEquiv F G g))).comp
    (GenericLie.equiv 𝒪[F] G).toLinearMap

theorem adjointF_apply (g : rationalPoints G) (X : GenericLie 𝒪[F] G) :
    adjointF g X = GenericLie.adjoint 𝒪[F] g X := rfl

theorem adjointF_mul (g h : rationalPoints G) (X : GenericLie 𝒪[F] G) :
    adjointF (g * h) X = adjointF g (adjointF h X) :=
  GenericLie.adjoint_mul 𝒪[F] g h X

theorem adjointF_one (X : GenericLie 𝒪[F] G) : adjointF (1 : rationalPoints G) X = X :=
  GenericLie.adjoint_one 𝒪[F] X

theorem adjointF_inv_apply (g : rationalPoints G) (X : GenericLie 𝒪[F] G) :
    adjointF g⁻¹ (adjointF g X) = X := by
  rw [← adjointF_mul, inv_mul_cancel, adjointF_one]

/-! ### The coadjoint action -/

/-- The coadjoint action `X ↦ X ∘ Ad(g⁻¹)` of `g ∈ G(F)` on `𝔤* = Module.Dual F 𝔤`. -/
def coadjoint (g : rationalPoints G) :
    Module.Dual F (GenericLie 𝒪[F] G) →ₗ[F] Module.Dual F (GenericLie 𝒪[F] G) :=
  (adjointF g⁻¹).dualMap

theorem coadjoint_apply (g : rationalPoints G) (X : Module.Dual F (GenericLie 𝒪[F] G))
    (Y : GenericLie 𝒪[F] G) : coadjoint g X Y = X (GenericLie.adjoint 𝒪[F] g⁻¹ Y) := rfl

theorem coadjoint_mul (g h : rationalPoints G) (X : Module.Dual F (GenericLie 𝒪[F] G)) :
    coadjoint (g * h) X = coadjoint g (coadjoint h X) := by
  refine LinearMap.ext fun Y => ?_
  rw [coadjoint_apply, coadjoint_apply, coadjoint_apply, mul_inv_rev, GenericLie.adjoint_mul]

theorem coadjoint_one (X : Module.Dual F (GenericLie 𝒪[F] G)) :
    coadjoint (1 : rationalPoints G) X = X := by
  refine LinearMap.ext fun Y => ?_
  rw [coadjoint_apply, inv_one, GenericLie.adjoint_one]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] {P : ParahoricBuildingData G}
  (L : P.LieFiltrationData)

/-! ### The stabilizer of the filtration -/

/-- The `g ∈ G(F)` such that `Ad(g)` and `Ad(g⁻¹)` map every `𝔤_{x,r}`, `r ≥ 0`, into itself. -/
def filtrationStabilizer (x : P.Apartment) : Subgroup (rationalPoints G) where
  carrier := {g | ∀ (r : NNReal), ∀ X ∈ L.lieFiltration x r,
    GenericLie.adjoint 𝒪[F] g X ∈ L.lieFiltration x r ∧
      GenericLie.adjoint 𝒪[F] g⁻¹ X ∈ L.lieFiltration x r}
  mul_mem' := by
    intro g h hg hh r X hX
    refine ⟨?_, ?_⟩
    · rw [GenericLie.adjoint_mul]
      exact (hg r _ (hh r X hX).1).1
    · rw [mul_inv_rev, GenericLie.adjoint_mul]
      exact (hh r _ (hg r X hX).2).2
  one_mem' := by
    intro r X hX
    simp only [inv_one, GenericLie.adjoint_one]
    exact ⟨hX, hX⟩
  inv_mem' := by
    intro g hg r X hX
    simp only [inv_inv]
    exact ⟨(hg r X hX).2, (hg r X hX).1⟩

variable {L}

theorem adjoint_mem_lieFiltration {x : P.Apartment} {g : rationalPoints G}
    (hg : g ∈ L.filtrationStabilizer x) {r : NNReal} {X : GenericLie 𝒪[F] G}
    (hX : X ∈ L.lieFiltration x r) : GenericLie.adjoint 𝒪[F] g X ∈ L.lieFiltration x r :=
  (hg r X hX).1

/-- The stabilizer also stabilizes the real-depth lattices. -/
theorem adjoint_mem_lieFiltrationReal {x : P.Apartment} {g : rationalPoints G}
    (hg : g ∈ L.filtrationStabilizer x) {r : ℝ} {X : GenericLie 𝒪[F] G}
    (hX : X ∈ L.lieFiltrationReal x r) : GenericLie.adjoint 𝒪[F] g X ∈ L.lieFiltrationReal x r := by
  rw [mem_lieFiltrationReal] at hX ⊢
  intro a ha
  rw [← map_smul]
  exact adjoint_mem_lieFiltration hg (hX a ha)

theorem adjoint_mem_lieFiltrationPlusReal {x : P.Apartment} {g : rationalPoints G}
    (hg : g ∈ L.filtrationStabilizer x) {r : ℝ} {X : GenericLie 𝒪[F] G}
    (hX : X ∈ L.lieFiltrationPlusReal x r) :
    GenericLie.adjoint 𝒪[F] g X ∈ L.lieFiltrationPlusReal x r := by
  have h : L.lieFiltrationPlusReal x r ≤
      (L.lieFiltrationPlusReal x r).comap (GenericLie.adjoint 𝒪[F] g) :=
    iSup₂_le fun s hs Y hY =>
      L.lieFiltrationReal_le_lieFiltrationPlusReal x hs (adjoint_mem_lieFiltrationReal hg hY)
  exact h hX

/-! ### The graded pieces of the Lie filtration -/

variable (L)

/-- The strict graded piece for real `r`, as an `𝒪[F]`-module: the quotient of `𝔤_{x,r}` by the
inverse image of `𝔤_{x,r+}`, that is by `𝔤_{x,r} ∩ 𝔤_{x,r+}`. Under `IsPeriodic`,
`𝔤_{x,r+} ≤ 𝔤_{x,r}` (`lieFiltrationPlusReal_le`) and `𝔤_{x,r+}` is KP's union
(`mem_lieFiltrationPlusReal`), so this is KP's `𝔤_{x,r}/𝔤_{x,r+}`. -/
abbrev gradedLie (x : P.Apartment) (r : ℝ) : Type u :=
  L.lieFiltrationReal x r ⧸ (L.lieFiltrationPlusReal x r).comap (L.lieFiltrationReal x r).subtype

/-- The action of an element of the stabilizer on `𝔤_{x,r}/𝔤_{x,r+}`. -/
def gradedAdjointMap (x : P.Apartment) (r : ℝ) (g : L.filtrationStabilizer x) :
    L.gradedLie x r →ₗ[𝒪[F]] L.gradedLie x r :=
  Submodule.mapQ _ _
    ((GenericLie.adjoint 𝒪[F] g.1).restrict fun _ hX => adjoint_mem_lieFiltrationReal g.2 hX)
    (fun _ hX => adjoint_mem_lieFiltrationPlusReal g.2 hX)

theorem gradedAdjointMap_mk (x : P.Apartment) (r : ℝ) (g : L.filtrationStabilizer x)
    (X : L.lieFiltrationReal x r) :
    L.gradedAdjointMap x r g (Submodule.Quotient.mk X) =
      Submodule.Quotient.mk ⟨GenericLie.adjoint 𝒪[F] g.1 X, adjoint_mem_lieFiltrationReal g.2 X.2⟩ :=
  rfl

/-- The representation of the stabilizer on `𝔤_{x,r}/𝔤_{x,r+}` (KP 13.3.4). -/
def gradedAdjoint (x : P.Apartment) (r : ℝ) :
    L.filtrationStabilizer x →* Module.End 𝒪[F] (L.gradedLie x r) where
  toFun := L.gradedAdjointMap x r
  map_one' := by
    refine LinearMap.ext fun Y => ?_
    obtain ⟨X, rfl⟩ := Submodule.Quotient.mk_surjective _ Y
    rw [gradedAdjointMap_mk]
    congr 1
    exact Subtype.ext (GenericLie.adjoint_one 𝒪[F] X.1)
  map_mul' g h := by
    refine LinearMap.ext fun Y => ?_
    obtain ⟨X, rfl⟩ := Submodule.Quotient.mk_surjective _ Y
    rw [Module.End.mul_apply, gradedAdjointMap_mk, gradedAdjointMap_mk, gradedAdjointMap_mk]
    congr 1
    exact Subtype.ext (GenericLie.adjoint_mul 𝒪[F] g.1 h.1 X.1)

/-! ### The dual lattices -/

variable {L}

/-- The stabilizer of the filtration stabilizes the dual lattices `𝔤*_{x,r}`. -/
theorem coadjoint_mem_dualLieFiltration {x : P.Apartment} {g : rationalPoints G}
    (hg : g ∈ L.filtrationStabilizer x) {r : ℝ} {X : Module.Dual F (GenericLie 𝒪[F] G)}
    (hX : X ∈ L.dualLieFiltration x r) : coadjoint g X ∈ L.dualLieFiltration x r := by
  rw [mem_dualLieFiltration] at hX ⊢
  intro s hs Y hY
  rw [coadjoint_apply]
  exact hX s hs _ (adjoint_mem_lieFiltrationReal (inv_mem hg) hY)

theorem coadjoint_mem_dualLieFiltrationPlus {x : P.Apartment} {g : rationalPoints G}
    (hg : g ∈ L.filtrationStabilizer x) {r : ℝ} {X : Module.Dual F (GenericLie 𝒪[F] G)}
    (hX : X ∈ L.dualLieFiltrationPlus x r) : coadjoint g X ∈ L.dualLieFiltrationPlus x r := by
  have h : L.dualLieFiltrationPlus x r ≤
      (L.dualLieFiltrationPlus x r).comap ((coadjoint g).restrictScalars 𝒪[F]) :=
    iSup₂_le fun s hs Y hY =>
      le_iSup₂_of_le (f := fun s (_ : r < s) => L.dualLieFiltration x s) s hs le_rfl
        (coadjoint_mem_dualLieFiltration hg hY)
  exact h hX

variable (L)

/-- The coadjoint action of an element of the stabilizer on `𝔤* ⧸ 𝔤*_{x,r+}`. -/
def coadjointQuot (x : P.Apartment) (r : ℝ) (g : L.filtrationStabilizer x) :
    (Module.Dual F (GenericLie 𝒪[F] G) ⧸ L.dualLieFiltrationPlus x r) →ₗ[𝒪[F]]
      (Module.Dual F (GenericLie 𝒪[F] G) ⧸ L.dualLieFiltrationPlus x r) :=
  Submodule.mapQ _ _ ((coadjoint g.1).restrictScalars 𝒪[F])
    (fun _ hX => coadjoint_mem_dualLieFiltrationPlus g.2 hX)

theorem coadjointQuot_mk (x : P.Apartment) (r : ℝ) (g : L.filtrationStabilizer x)
    (X : Module.Dual F (GenericLie 𝒪[F] G)) :
    L.coadjointQuot x r g (Submodule.Quotient.mk X) = Submodule.Quotient.mk (coadjoint g.1 X) :=
  rfl

/-- The strict graded piece `𝔤*_{x,r}/𝔤*_{x,r+}` for real `r`, realized as the image of
`𝔤*_{x,r}` in `𝔤* ⧸ 𝔤*_{x,r+}`. -/
def dualGradedLie (x : P.Apartment) (r : ℝ) :
    Submodule 𝒪[F] (Module.Dual F (GenericLie 𝒪[F] G) ⧸ L.dualLieFiltrationPlus x r) :=
  (L.dualLieFiltration x r).map (L.dualLieFiltrationPlus x r).mkQ

theorem coadjointQuot_mem_dualGradedLie {x : P.Apartment} {r : ℝ} (g : L.filtrationStabilizer x)
    {Y : Module.Dual F (GenericLie 𝒪[F] G) ⧸ L.dualLieFiltrationPlus x r}
    (hY : Y ∈ L.dualGradedLie x r) : L.coadjointQuot x r g Y ∈ L.dualGradedLie x r := by
  obtain ⟨X, hX, rfl⟩ := Submodule.mem_map.1 hY
  exact Submodule.mem_map.2 ⟨_, coadjoint_mem_dualLieFiltration g.2 hX, rfl⟩

/-- The representation of the stabilizer on `𝔤*_{x,r}/𝔤*_{x,r+}` (KP 13.3.4). -/
def dualGradedAdjoint (x : P.Apartment) (r : ℝ) :
    L.filtrationStabilizer x →* Module.End 𝒪[F] (L.dualGradedLie x r) where
  toFun g := (L.coadjointQuot x r g).restrict fun _ hY => L.coadjointQuot_mem_dualGradedLie g hY
  map_one' := by
    refine LinearMap.ext fun Y => Subtype.ext ?_
    obtain ⟨X, -, hX⟩ := Submodule.mem_map.1 Y.2
    rw [LinearMap.coe_restrict_apply, Module.End.one_apply, ← hX, Submodule.mkQ_apply,
      coadjointQuot_mk]
    exact congrArg _ (coadjoint_one X)
  map_mul' g h := by
    refine LinearMap.ext fun Y => Subtype.ext ?_
    obtain ⟨X, -, hX⟩ := Submodule.mem_map.1 Y.2
    rw [Module.End.mul_apply, LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply,
      LinearMap.coe_restrict_apply, ← hX, Submodule.mkQ_apply, coadjointQuot_mk, coadjointQuot_mk,
      coadjointQuot_mk]
    exact congrArg _ (coadjoint_mul g.1 h.1 X)

theorem dualGradedAdjoint_apply (x : P.Apartment) (r : ℝ) (g : L.filtrationStabilizer x)
    (Y : L.dualGradedLie x r) : (L.dualGradedAdjoint x r g Y : _) = L.coadjointQuot x r g Y :=
  rfl

/-! ### Restriction to a subgroup and factorization through a quotient -/

/-- The representation of a subgroup `H ≤ filtrationStabilizer x` (for instance the parahoric
subgroup `P_x`) on `𝔤_{x,r}/𝔤_{x,r+}`. -/
def subgroupGradedAdjoint (x : P.Apartment) (r : ℝ) {H : Subgroup (rationalPoints G)}
    (hH : H ≤ L.filtrationStabilizer x) : H →* Module.End 𝒪[F] (L.gradedLie x r) :=
  (L.gradedAdjoint x r).comp (Subgroup.inclusion hH)

/-- The representation of a subgroup `H ≤ filtrationStabilizer x` on `𝔤*_{x,r}/𝔤*_{x,r+}`. -/
def subgroupDualGradedAdjoint (x : P.Apartment) (r : ℝ) {H : Subgroup (rationalPoints G)}
    (hH : H ≤ L.filtrationStabilizer x) : H →* Module.End 𝒪[F] (L.dualGradedLie x r) :=
  (L.dualGradedAdjoint x r).comp (Subgroup.inclusion hH)

/-- `N` acts trivially on `𝔤_{x,r}/𝔤_{x,r+}`: `Ad(n) X - X ∈ 𝔤_{x,r+}` for `X ∈ 𝔤_{x,r}`. -/
def ActsTriviallyOnGraded (x : P.Apartment) (r : ℝ) (N : Subgroup (rationalPoints G)) : Prop :=
  ∀ n ∈ N, ∀ X ∈ L.lieFiltrationReal x r,
    GenericLie.adjoint 𝒪[F] n X - X ∈ L.lieFiltrationPlusReal x r

/-- `N` acts trivially on `𝔤*_{x,r}/𝔤*_{x,r+}`. -/
def ActsTriviallyOnDualGraded (x : P.Apartment) (r : ℝ) (N : Subgroup (rationalPoints G)) : Prop :=
  ∀ n ∈ N, ∀ X ∈ L.dualLieFiltration x r, coadjoint n X - X ∈ L.dualLieFiltrationPlus x r

/-- The real-depth filtration is left-continuous at `t` if `𝔤_{x,u} ⊆ 𝔤_{x,t}` (hence, for a
decreasing filtration, `𝔤_{x,u} = 𝔤_{x,t}`) for all `u` in some interval `(s, t]`. -/
def IsLeftContinuousAt (x : P.Apartment) (t : ℝ) : Prop :=
  ∃ s < t, ∀ u, s < u → u ≤ t → L.lieFiltrationReal x u ≤ L.lieFiltrationReal x t

variable {L}

/-- Under periodicity and left continuity at `t`, `𝔤_{x,s+} ⊆ 𝔤_{x,t}` for some `s < t`. -/
theorem exists_lieFiltrationPlusReal_le (hL : L.IsPeriodic) {x : P.Apartment} {t : ℝ}
    (hc : L.IsLeftContinuousAt x t) :
    ∃ s < t, L.lieFiltrationPlusReal x s ≤ L.lieFiltrationReal x t := by
  obtain ⟨s, hs, h⟩ := hc
  refine ⟨s, hs, iSup₂_le fun u hu => ?_⟩
  rcases le_or_gt u t with hut | htu
  · exact h u hu hut
  · exact L.lieFiltrationReal_antitone hL x htu.le

/-- Transfer of triviality to the dual graded piece: if `N` acts trivially on
`𝔤_{x,-r}/𝔤_{x,(-r)+}` and `𝔤_{x,s+} ⊆ 𝔤_{x,-r}` for some `s < -r`, then `N` acts trivially on
`𝔤*_{x,r}/𝔤*_{x,r+}`. Indeed `(n·X - X)(Y) = X(Ad(n⁻¹) Y - Y) ∈ 𝔪` for `Y ∈ 𝔤_{x,s+}`, so
`n·X - X ∈ 𝔤*_{x,-s} ⊆ 𝔤*_{x,r+}`. -/
theorem actsTriviallyOnDualGraded_of_lieFiltrationPlusReal_le {x : P.Apartment} {r s : ℝ}
    {N : Subgroup (rationalPoints G)} (hN : L.ActsTriviallyOnGraded x (-r) N) (hs : s < -r)
    (hle : L.lieFiltrationPlusReal x s ≤ L.lieFiltrationReal x (-r)) :
    L.ActsTriviallyOnDualGraded x r N := by
  intro n hn X hX
  refine L.mem_dualLieFiltrationPlus.2 ⟨-s, by linarith, ?_⟩
  rw [mem_dualLieFiltration]
  intro t ht Y hY
  rw [neg_neg] at ht
  have hY' : Y ∈ L.lieFiltrationReal x (-r) :=
    hle (L.lieFiltrationReal_le_lieFiltrationPlusReal x ht hY)
  have hX' : L.lieFiltrationPlusReal x (-r) ≤ dualPairingSubmodule X := hX
  obtain ⟨m, hm, e⟩ := (mem_dualPairingSubmodule X _).1 (hX' (hN n⁻¹ (inv_mem hn) Y hY'))
  refine ⟨m, hm, ?_⟩
  rw [e, LinearMap.sub_apply, coadjoint_apply, map_sub]

/-- Under periodicity and left continuity at `-r`, triviality of `N` on `𝔤_{x,-r}/𝔤_{x,(-r)+}`
implies triviality on `𝔤*_{x,r}/𝔤*_{x,r+}`. -/
theorem actsTriviallyOnDualGraded_of_isLeftContinuousAt (hL : L.IsPeriodic) {x : P.Apartment}
    {r : ℝ} {N : Subgroup (rationalPoints G)} (hc : L.IsLeftContinuousAt x (-r))
    (hN : L.ActsTriviallyOnGraded x (-r) N) : L.ActsTriviallyOnDualGraded x r N := by
  obtain ⟨s, hs, hle⟩ := exists_lieFiltrationPlusReal_le hL hc
  exact actsTriviallyOnDualGraded_of_lieFiltrationPlusReal_le hN hs hle

variable (L)

theorem le_ker_subgroupGradedAdjoint {x : P.Apartment} {r : ℝ} {H N : Subgroup (rationalPoints G)}
    (hH : H ≤ L.filtrationStabilizer x) (hN : L.ActsTriviallyOnGraded x r N) :
    N.subgroupOf H ≤ (L.subgroupGradedAdjoint x r hH).ker := by
  intro h hh
  rw [MonoidHom.mem_ker]
  refine LinearMap.ext fun Y => ?_
  obtain ⟨X, rfl⟩ := Submodule.Quotient.mk_surjective _ Y
  change L.gradedAdjointMap x r _ _ = _
  rw [gradedAdjointMap_mk, Module.End.one_apply, Submodule.Quotient.eq]
  exact hN h.1 hh X.1 X.2

theorem le_ker_subgroupDualGradedAdjoint {x : P.Apartment} {r : ℝ}
    {H N : Subgroup (rationalPoints G)} (hH : H ≤ L.filtrationStabilizer x)
    (hN : L.ActsTriviallyOnDualGraded x r N) :
    N.subgroupOf H ≤ (L.subgroupDualGradedAdjoint x r hH).ker := by
  intro h hh
  rw [MonoidHom.mem_ker]
  refine LinearMap.ext fun Y => Subtype.ext ?_
  obtain ⟨X, hX, hXY⟩ := Submodule.mem_map.1 Y.2
  change L.coadjointQuot x r _ Y.1 = Y.1
  rw [← hXY, Submodule.mkQ_apply, coadjointQuot_mk, Submodule.Quotient.eq]
  exact hN h.1 hh X hX

/-- The representation of `H ⧸ N` on `𝔤_{x,r}/𝔤_{x,r+}` when `N` acts trivially; with `H = P_x`
and `N = P_{x,0+}` this is the action of `P_x/P_{x,0+}` of KP 13.3.4. -/
def quotientGradedAdjoint (x : P.Apartment) (r : ℝ) {H N : Subgroup (rationalPoints G)}
    (hH : H ≤ L.filtrationStabilizer x) (hN : L.ActsTriviallyOnGraded x r N)
    [(N.subgroupOf H).Normal] : H ⧸ N.subgroupOf H →* Module.End 𝒪[F] (L.gradedLie x r) :=
  QuotientGroup.lift _ (L.subgroupGradedAdjoint x r hH) (L.le_ker_subgroupGradedAdjoint hH hN)

/-- The representation of `H ⧸ N` on `𝔤*_{x,r}/𝔤*_{x,r+}` when `N` acts trivially. -/
def quotientDualGradedAdjoint (x : P.Apartment) (r : ℝ) {H N : Subgroup (rationalPoints G)}
    (hH : H ≤ L.filtrationStabilizer x) (hN : L.ActsTriviallyOnDualGraded x r N)
    [(N.subgroupOf H).Normal] : H ⧸ N.subgroupOf H →* Module.End 𝒪[F] (L.dualGradedLie x r) :=
  QuotientGroup.lift _ (L.subgroupDualGradedAdjoint x r hH)
    (L.le_ker_subgroupDualGradedAdjoint hH hN)

theorem quotientGradedAdjoint_mk (x : P.Apartment) (r : ℝ) {H N : Subgroup (rationalPoints G)}
    (hH : H ≤ L.filtrationStabilizer x) (hN : L.ActsTriviallyOnGraded x r N)
    [(N.subgroupOf H).Normal] (h : H) :
    L.quotientGradedAdjoint x r hH hN (QuotientGroup.mk h) = L.subgroupGradedAdjoint x r hH h :=
  rfl

end Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData
