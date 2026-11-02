import Langlands.AlgebraicGeometry.Picard.AmplePowerTwistStatement
import Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingProof
import Langlands.AlgebraicGeometry.Modules.QuasiAffineLineBundleSectionBasis
import Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenBasisProof
import Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleProof
import Langlands.AlgebraicGeometry.Picard.LineBundleFiniteMonoDetector
import Langlands.AlgebraicGeometry.Picard.AmpleTensorProof

/-!
# Twisting by a large power of an ample line bundle

For an ample line bundle `H` and any line bundle `N`, every line bundle isomorphic to
`N ⊗ H^{⊗ b}` is ample once `b` is large. The proof extends sections of a twisted
tower from a generation open (Stacks Lemma 18.2, tag 01PW, for a twist) to find,
at every point, a section of some `N ⊗ H^{⊗ c}` generating there. It then applies a
pointwise form of Stacks Lemma 27.5 (tag 0890) with the ample bundle `H^{⊗ (b - c)}`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.SchemeModule.SectionClearing

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.AmplePowerTwist

variable {X : Scheme.{u}}

/-! ### Gluing a family of sections given over an open -/

section Gluing

variable {N : ℕ → X.Modules} {μ : ∀ m, N m ⟶ N (m + 1)}

/-- Iterated multiplication sends the `n`-th member of a compatible family over `U` to
the `(n + k)`-th. -/
lemma powMul_app_family {U : X.Opens} (p : ∀ m, Γ(N m, U))
    (hp : ∀ m, (μ m).app U (p m) = p (m + 1)) (n k : ℕ) :
    (powMul N μ n k).app U (p n) = p (n + k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [powMul_succ_app, ih]
    exact hp (n + k)

/-- Multiplying a local extension by powers of the section gives local extensions. -/
lemma powMul_extends {U : X.Opens} (p : ∀ m, Γ(N m, U))
    (hp : ∀ m, (μ m).app U (p m) = p (m + 1)) {V : X.Opens} {n : ℕ} (b : Γ(N n, V))
    (hb : (N n).presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op b =
      (N n).presheaf.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op (p n)) (k : ℕ) :
    (N (n + k)).presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op
        ((powMul N μ n k).app V b) =
      (N (n + k)).presheaf.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op (p (n + k)) := by
  rw [← hom_app_map, hb, hom_app_map, powMul_app_family p hp]

section Chart

variable {T : X.Opens} {c : Γ(X, T)} (C : LocalChart N μ T c)

include C

/-- In a chart, the coordinates of a compatible family are those of its first member
times powers of the chart coefficient. -/
lemma chart_E_family {U : X.Opens} (p : ∀ m, Γ(N m, U))
    (hp : ∀ m, (μ m).app U (p m) = p (m + 1))
    {W : X.Opens} (hWT : W ≤ T) (hWU : W ≤ U) (m : ℕ) :
    C.E m W hWT ((N m).presheaf.map (homOfLE hWU).op (p m)) =
      C.E 0 W hWT ((N 0).presheaf.map (homOfLE hWU).op (p 0)) *
        (X.presheaf.map (homOfLE hWT).op c) ^ m := by
  induction m with
  | zero => rw [pow_zero, mul_one]
  | succ m ih =>
    rw [← hp m, ← hom_app_map, C.mul, ih, pow_succ, mul_assoc]

/-- On an affine open inside the chart, a member of the family extends from `V ⊓ U`
to `V`. -/
lemma chart_exists_local_family {U : X.Opens} (p : ∀ m, Γ(N m, U))
    (hp : ∀ m, (μ m).app U (p m) = p (m + 1)) (hc : X.basicOpen c = T ⊓ U) {V : X.Opens}
    (hV : IsAffineOpen V) (hVT : V ≤ T) :
    ∃ (n : ℕ) (b : Γ(N n, V)), (N n).presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op b =
      (N n).presheaf.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op (p n) := by
  have hB : X.basicOpen (X.presheaf.map (homOfLE hVT).op c) = V ⊓ U := by
    rw [Scheme.basicOpen_res, hc, ← inf_assoc, inf_eq_left.mpr hVT]
  have hVU : V ⊓ U ≤ T := inf_le_left.trans hVT
  obtain ⟨f, hf⟩ : ∃ f : Γ(X, V ⊓ U),
      f = C.E 0 (V ⊓ U) hVU ((N 0).presheaf.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op (p 0)) :=
    ⟨_, rfl⟩
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X V hV
    (X.presheaf.map (homOfLE hVT).op c) (X.presheaf.map (homOfLE hB.le).op f)
  have hy' : X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op y =
      (X.presheaf.map (homOfLE hVU).op c) ^ n * f := by
    have := congrArg (fun z => X.presheaf.map (homOfLE hB.ge).op z) hy
    dsimp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] at this
    simpa only [map_mul, map_pow, presheaf_map_map, presheaf_map_id] using this
  obtain ⟨b, hb⟩ := C.surjective n V hVT y
  refine ⟨n, b, C.injective n (V ⊓ U) hVU ?_⟩
  rw [C.res n V (V ⊓ U) hVT inf_le_left, hb, hy', chart_E_family C p hp hVU inf_le_right n, ← hf]
  exact mul_comm _ _

end Chart

/-- Gluing the local extensions provided by charts around every point: on a quasi-compact
quasi-separated scheme, some member of a compatible family of sections over `U` is the
restriction of a global section. -/
theorem exists_global_of_charts_family [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (p : ∀ m, Γ(N m, U)) (hp : ∀ m, (μ m).app U (p m) = p (m + 1))
    (hchart : ∀ x : X, ∃ (T : X.Opens) (c : Γ(X, T)), x ∈ T ∧ X.basicOpen c = T ⊓ U ∧
      Nonempty (LocalChart N μ T c)) :
    ∃ (m : ℕ) (a : Γ(N m, ⊤)), (N m).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a = p m := by
  choose T c hxT hc hC using hchart
  have hV : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ T x := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVT⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hxT x) (T x).2
    exact ⟨V, hV, hxV, hVT⟩
  choose V hVa hxV hVT using hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).2) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have hcov : ∀ y : X, ∃ i : t, y ∈ V i.1 := fun y => by
    have hy := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    exact ⟨⟨x, hx⟩, hyx⟩
  -- Step 1: local extensions with a common exponent.
  have h1 : ∀ i : t, ∀ᶠ n in Filter.atTop, ∃ b : Γ(N n, V i.1),
      (N n).presheaf.map (homOfLE (inf_le_left : V i.1 ⊓ U ≤ V i.1)).op b =
        (N n).presheaf.map (homOfLE (inf_le_right : V i.1 ⊓ U ≤ U)).op (p n) := fun i => by
    obtain ⟨n₀, b₀, hb₀⟩ :=
      chart_exists_local_family (hC i.1).some p hp (hc i.1) (hVa i.1) (hVT i.1)
    refine Filter.eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact ⟨_, powMul_extends p hp b₀ hb₀ k⟩
  obtain ⟨e, he⟩ := (Filter.eventually_all.2 h1).exists
  choose b hb using he
  -- Step 2: kill the differences on the overlaps.
  have h2 : ∀ ij : t × t, ∀ᶠ k in Filter.atTop,
      (powMul N μ e k).app (V ij.1.1 ⊓ V ij.2.1)
        ((N e).presheaf.map (homOfLE (inf_le_left : V ij.1.1 ⊓ V ij.2.1 ≤ V ij.1.1)).op
            (b ij.1) -
          (N e).presheaf.map (homOfLE (inf_le_right : V ij.1.1 ⊓ V ij.2.1 ≤ V ij.2.1)).op
            (b ij.2)) = 0 := fun ij => by
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := ij
    have hcpt : IsCompact ((V i ⊓ V j : X.Opens) : Set X) :=
      (hVa i).isCompact.inter_of_isOpen (hVa j).isCompact (V i).2 (V j).2
    have hd : (N e).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ⊓ U ≤ V i ⊓ V j)).op
        ((N e).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b ⟨i, hi⟩) -
          (N e).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b ⟨j, hj⟩)) =
        0 := by
      rw [map_sub, modules_map_map, modules_map_map]
      have e1 := congrArg (fun z => (N e).presheaf.map
        (homOfLE (show V i ⊓ V j ⊓ U ≤ V i ⊓ U from
          inf_le_inf_right U inf_le_left)).op z) (hb ⟨i, hi⟩)
      have e2 := congrArg (fun z => (N e).presheaf.map
        (homOfLE (show V i ⊓ V j ⊓ U ≤ V j ⊓ U from
          inf_le_inf_right U inf_le_right)).op z) (hb ⟨j, hj⟩)
      simp only [modules_map_map] at e1 e2
      rw [e1, e2, sub_self]
    obtain ⟨k₀, hk₀⟩ := (hC i).some.exists_powMul_eq_zero U (hc i)
      (inf_le_left.trans (hVT i)) hcpt _ hd
    exact Filter.eventually_atTop.2 ⟨k₀, fun k hk => powMul_app_eq_zero_of_le hk₀ hk⟩
  obtain ⟨k, hk⟩ := (Filter.eventually_all.2 h2).exists
  -- Step 3: glue.
  let F : TopCat.Sheaf Ab X := ⟨(N (e + k)).presheaf, (N (e + k)).isSheaf⟩
  let a' : ∀ i : t, Γ(N (e + k), V i.1) := fun i => (powMul N μ e k).app (V i.1) (b i)
  have hcompat : TopCat.Presheaf.IsCompatible F.1 (fun i : t => V i.1) a' := by
    intro i j
    have := hk (i, j)
    rw [map_sub, sub_eq_zero, hom_app_map, hom_app_map] at this
    exact this
  have hcover : (⊤ : X.Opens) ≤ iSup (fun i : t => V i.1) := by
    intro y _
    obtain ⟨i, hi⟩ := hcov y
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨a, ha, -⟩ := F.existsUnique_gluing' (fun i : t => V i.1) ⊤
    (fun i => homOfLE le_top) hcover a' hcompat
  refine ⟨e + k, a, ?_⟩
  have hcoverU : U ≤ iSup (fun i : t => V i.1 ⊓ U) := by
    intro y hy
    obtain ⟨i, hi⟩ := hcov y
    exact Opens.mem_iSup.2 ⟨i, hi, hy⟩
  refine F.eq_of_locally_eq' (fun i : t => V i.1 ⊓ U) U (fun i => homOfLE inf_le_right)
    hcoverU _ _ (fun i => ?_)
  change (N (e + k)).presheaf.map (homOfLE inf_le_right).op
      ((N (e + k)).presheaf.map (homOfLE le_top).op a) =
    (N (e + k)).presheaf.map (homOfLE inf_le_right).op (p (e + k))
  have hai : (N (e + k)).presheaf.map (homOfLE (le_top : V i.1 ≤ ⊤)).op a = a' i := ha i
  rw [modules_map_map, ← modules_map_map (N (e + k)) (le_top : V i.1 ≤ ⊤) inf_le_left, hai]
  exact powMul_extends p hp (b i) (hb i) k

end Gluing

/-! ### The twisted tower `L ⊗ (L ⊗ ⋯ (L ⊗ F))` -/

section Twist

variable (L F : X.Modules)

/-- The twisted tower: `twistPow L F m = L ⊗ (L ⊗ ⋯ (L ⊗ F))` with `m` factors `L`. -/
def twistPow : ℕ → X.Modules
  | 0 => F
  | m + 1 => tensorObj L (twistPow m)

/-- Multiplication by a global section `s` of `L` along the twisted tower. -/
def twistMul (s : GlobalSections L) (m : ℕ) : twistPow L F m ⟶ twistPow L F (m + 1) :=
  sectionMul L s (twistPow L F m)

/-- The family `s^m q` over `U` obtained from a section `q` of `F` over `U`. -/
def twistFamily (s : GlobalSections L) {U : X.Opens} (q : Γ(F, U)) :
    (m : ℕ) → Γ(twistPow L F m, U)
  | 0 => q
  | m + 1 => (twistMul L F s m).app U (twistFamily s q m)

/-- The twisted tower is isomorphic to `F ⊗ L^{⊗ m}`. -/
lemma nonempty_twistPow_iso (m : ℕ) :
    Nonempty (twistPow L F m ≅ tensorObj F (tensorPow L m)) := by
  induction m with
  | zero => exact ⟨(tensorRightUnitor F).symm⟩
  | succ m ih =>
    obtain ⟨i⟩ := ih
    exact ⟨(tensorFunctor X).mapIso ((Iso.refl L).prod i) ≪≫
      (tensorAssociator L F (tensorPow L m)).symm ≪≫
      (tensorFunctor X).mapIso ((tensorComm L F).prod (Iso.refl _)) ≪≫
      tensorAssociator F L (tensorPow L m)⟩

variable (T : X.Opens) (e : L.restrict T.ι ≅ SheafOfModules.unit T.toScheme.ringCatSheaf)
  (eF : F.restrict T.ι ≅ SheafOfModules.unit T.toScheme.ringCatSheaf)

/-- The trivializations of the pulled-back twisted tower induced by trivializations of
`L` and `F` over `T`. -/
def twistTriv : (m : ℕ) →
    ((Scheme.Modules.pullback T.ι).obj (twistPow L F m) ≅ structureSheaf T.toScheme)
  | 0 => pullbackTriv T F eF
  | m + 1 => pullbackTensorIso T L (twistPow L F m) ≪≫
      (tensorFunctor T.toScheme).mapIso ((pullbackTriv T L e).prod (twistTriv m)) ≪≫
      tensorLeftUnitor (structureSheaf T.toScheme)

/-- The trivializations of the restricted twisted tower. -/
def twistChartIso (m : ℕ) : (twistPow L F m).restrict T.ι ≅ structureSheaf T.toScheme :=
  (Scheme.Modules.restrictFunctorIsoPullback T.ι).app (twistPow L F m) ≪≫
    twistTriv L F T e eF m

/-- Multiplication by `s` is `chartMulOf (sectionHom L s)` in the trivializations. -/
lemma twistChartIso_succ (s : GlobalSections L) (m : ℕ) :
    (Scheme.Modules.restrictFunctor T.ι).map (twistMul L F s m) ≫
        (twistChartIso L F T e eF (m + 1)).hom =
      (twistChartIso L F T e eF m).hom ≫ chartMulOf T L e (sectionHom L s) := by
  simp only [twistChartIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback T.ι).hom.naturality,
    Category.assoc, Category.assoc]
  congr 1
  exact pullback_mul_comp T L e (sectionHom L s) (twistPow L F m) (twistTriv L F T e eF m)

end Twist

/-- The twisted tower of line bundles consists of line bundles. -/
lemma twistPow_isLocallyFreeRankOne (L F : LineBundle X) (m : ℕ) :
    IsLocallyFreeRankOne (twistPow L.obj F.obj m) := by
  induction m with
  | zero => exact F.property
  | succ m ih => exact L.property.tensor pullbackTensorComparisonIsIso ih

/-- **Extension along the twisted tower** (Stacks Lemma 18.2, tag 01PW, for a twist).
On a quasi-compact quasi-separated scheme, let `s` be a global section of a line bundle
`L` and let the line bundle `F` be trivial on the generation open `U = X_s`. Then some
stage of the twisted tower has a global section generating on all of `U`. -/
theorem exists_twist_section [CompactSpace X] [QuasiSeparatedSpace X] (L F : LineBundle X)
    (s : GlobalSections L.obj)
    (eFU : F.obj.restrict (trivializationOpen L.obj s).ι ≅
      SheafOfModules.unit (trivializationOpen L.obj s).toScheme.ringCatSheaf) :
    ∃ (m : ℕ) (a : GlobalSections (twistPow L.obj F.obj m)),
      trivializationOpen L.obj s ≤ trivializationOpen (twistPow L.obj F.obj m) a := by
  set U := trivializationOpen L.obj s with hU
  let eLU : L.obj.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    (trivializationOpenIso L.obj s).symm
  let CU := localChartOf (fun m => twistChartIso L.obj F.obj U eLU eFU m)
    (chartMulOf U L.obj eLU (sectionHom L.obj s)) (twistChartIso_succ L.obj F.obj U eLU eFU s)
  let q : Γ(F.obj, U) := chartF (twistChartIso L.obj F.obj U eLU eFU 0) U le_rfl 1
  have hchart : ∀ x : X, ∃ (T : X.Opens) (c : Γ(X, T)), x ∈ T ∧ X.basicOpen c = T ⊓ U ∧
      Nonempty (LocalChart (twistPow L.obj F.obj) (twistMul L.obj F.obj s) T c) := by
    intro x
    obtain ⟨T₁, hx₁, ⟨e₁⟩⟩ := L.property x
    obtain ⟨T₂, hx₂, ⟨e₂⟩⟩ := F.property x
    let eL := restrictTrivializationOfLE (inf_le_left : T₁ ⊓ T₂ ≤ T₁) e₁
    let eF := restrictTrivializationOfLE (inf_le_right : T₁ ⊓ T₂ ≤ T₂) e₂
    exact ⟨T₁ ⊓ T₂, _, ⟨hx₁, hx₂⟩, basicOpen_chartCoeff (T₁ ⊓ T₂) L s eL,
      ⟨localChartOf (fun m => twistChartIso L.obj F.obj (T₁ ⊓ T₂) eL eF m) _
        (twistChartIso_succ L.obj F.obj (T₁ ⊓ T₂) eL eF s)⟩⟩
  obtain ⟨m, a, ha⟩ := exists_global_of_charts_family U (twistFamily L.obj F.obj s q)
    (fun m => rfl) hchart
  refine ⟨m, a, ?_⟩
  -- On `U` the chart coefficient is a unit, and the coordinate of `a` is its `m`-th power.
  let cU := chartCoeff (chartMulOf U L.obj eLU (sectionHom L.obj s))
  have hcU : X.basicOpen cU = U ⊓ U := basicOpen_chartCoeff U L s eLU
  have hDU : X.basicOpen cU ≤ U := X.basicOpen_le cU
  let M' : LineBundle X := ⟨twistPow L.obj F.obj m, twistPow_isLocallyFreeRankOne L F m⟩
  have hres : sectionRes M'.obj a (X.basicOpen cU) =
      (twistPow L.obj F.obj m).presheaf.map (homOfLE hDU).op
        (twistFamily L.obj F.obj s q m) := by
    rw [← ha, modules_map_map]
  have hq : CU.E 0 U le_rfl q = 1 := chartE_chartF _ U le_rfl 1
  have hcoord : chartE (twistChartIso L.obj F.obj U eLU eFU m) (X.basicOpen cU) hDU
      (sectionRes M'.obj a (X.basicOpen cU)) = (X.presheaf.map (homOfLE hDU).op cU) ^ m := by
    change CU.E m (X.basicOpen cU) hDU (sectionRes M'.obj a (X.basicOpen cU)) = _
    rw [hres, chart_E_family CU (twistFamily L.obj F.obj s q) (fun m => rfl) hDU hDU m]
    have h0 := CU.res 0 U (X.basicOpen cU) le_rfl hDU q
    rw [show twistFamily L.obj F.obj s q 0 = q from rfl, h0, hq, map_one, one_mul]
  have hD : X.basicOpen cU ≤ trivializationOpen M'.obj a :=
    QuasiAffineSectionBasis.le_trivializationOpen_of_chart_unit M'
      (twistChartIso L.obj F.obj U eLU eFU m) hDU a
      (by rw [hcoord]; exact (X.toRingedSpace.isUnit_res_basicOpen cU).pow m)
  exact (le_inf le_rfl le_rfl).trans (hcU.ge.trans hD)

/-- Every point lies in the generation open of a global section of some twist
`N ⊗ H^{⊗ c}` of a line bundle `N` by a power of an ample line bundle `H`. -/
theorem exists_twist_section_mem (X : Scheme.{u}) (H N : LineBundle X) (hH : H.IsAmple)
    (x : X) :
    ∃ (c : ℕ) (t : GlobalSections (tensorObj N.obj (tensorPow H.obj c))),
      x ∈ trivializationOpen (tensorObj N.obj (tensorPow H.obj c)) t := by
  have : CompactSpace X := hH.compactSpace
  have : QuasiSeparatedSpace X := hH.quasiSeparatedSpace
  obtain ⟨T, hxT, ⟨eT⟩⟩ := N.property x
  obtain ⟨d, -, s, hxs, hsT⟩ := ampleSectionOpenBasis X H hH T x hxT
  let Hd : LineBundle X := ⟨tensorPow H.obj d, tensorPow_isLocallyFreeRankOne X H d⟩
  obtain ⟨m, a, ha⟩ := exists_twist_section Hd N s (restrictTrivializationOfLE hsT eT)
  obtain ⟨i⟩ := nonempty_twistPow_iso Hd.obj N.obj m
  let E : twistPow Hd.obj N.obj m ≅ tensorObj N.obj (tensorPow H.obj (d * m)) :=
    i ≪≫ (tensorFunctor X).mapIso ((Iso.refl N.obj).prod (tensorPowMulIso H.obj d m))
  refine ⟨d * m, E.hom.app ⊤ a, ?_⟩
  rw [trivializationOpen_mapIso]
  exact ha hxs

/-- **Pointwise form of Stacks Lemma 27.5 (tag 0890).** If `A` is ample, `M` has a global
section `t` generating at `y`, and `P ≅ A ⊗ M`, then `y` lies in an affine generation open
of a section of a positive tensor power of `P`. -/
theorem exists_affine_section_of_ample_tensor {X : Scheme.{u}} (A M P : LineBundle X)
    (e : P.obj ≅ tensorObj A.obj M.obj) (hA : A.IsAmple) (t : GlobalSections M.obj) {y : X}
    (hy : y ∈ trivializationOpen M.obj t) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ r : P.powSections n,
      y ∈ P.sectionOpen r ∧ IsAffineOpen (P.sectionOpen r) := by
  obtain ⟨n, hn, s, hys, hs⟩ := hA.2 y
  let An : LineBundle X := ⟨tensorPow A.obj n, tensorPow_isLocallyFreeRankOne X A n⟩
  let Mn : LineBundle X := ⟨tensorPow M.obj n, tensorPow_isLocallyFreeRankOne X M n⟩
  let tn : GlobalSections Mn.obj := sectionPow M.obj t n
  let q : GlobalSections (tensorObj An.obj Mn.obj) := tensorSection An.obj Mn.obj s tn
  let E : tensorObj An.obj Mn.obj ≅ tensorPow P.obj n :=
    (tensorPowTensorIso A.obj M.obj n).symm ≪≫ tensorPowIso e.symm n
  let r : P.powSections n := E.hom.app ⊤ q
  have htn : trivializationOpen Mn.obj tn = trivializationOpen M.obj t :=
    trivializationOpen_sectionPow M t hn
  have hopen : P.sectionOpen r = A.sectionOpen s ⊓ trivializationOpen M.obj t := by
    change trivializationOpen (tensorPow P.obj n) (E.hom.app ⊤ q) = _
    rw [trivializationOpen_mapIso E q]
    change trivializationOpen (tensorObj An.obj Mn.obj) (tensorSection An.obj Mn.obj s tn) = _
    rw [tensorSectionGenerationLocus X An Mn s tn, htn]
  refine ⟨n, hn, r, ?_, ?_⟩
  · rw [hopen]
    exact ⟨hys, hy⟩
  · rw [hopen]
    exact affineGenerationLocusIntersection X M t (A.sectionOpen s) hs

end Langlands.AlgebraicGeometry.Picard.AmplePowerTwist

namespace Langlands.AlgebraicGeometry.Picard

open AmplePowerTwist

/-- Twisting a line bundle by a large tensor power of an ample line bundle gives an ample
line bundle. -/
theorem amplePowerTwist : AmplePowerTwistStatement.{u} := by
  intro X H N hH
  have : CompactSpace X := hH.compactSpace
  choose c t ht using exists_twist_section_mem X H N hH
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (trivializationOpen (tensorObj N.obj (tensorPow H.obj (c x))) (t x) : Set X))
    (fun x => (trivializationOpen _ (t x)).2) (fun x _ => Set.mem_iUnion.2 ⟨x, ht x⟩)
  refine ⟨S.sup c + 1, fun b hb P ⟨eP⟩ => ⟨hH.1, fun y => ?_⟩⟩
  obtain ⟨x, hxS, hyx⟩ : ∃ x ∈ S,
      y ∈ (trivializationOpen (tensorObj N.obj (tensorPow H.obj (c x))) (t x) : Set X) := by
    have := hS (Set.mem_univ y)
    simpa only [Set.mem_iUnion, exists_prop] using this
  have hcb : c x < b := Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup hxS)) hb
  let A : LineBundle X :=
    ⟨tensorPow H.obj (b - c x), tensorPow_isLocallyFreeRankOne X H (b - c x)⟩
  have hA : A.IsAmple :=
    positiveTensorPowerAmple X H A (b - c x) (Nat.sub_pos_of_lt hcb) hH ⟨Iso.refl _⟩
  let M : LineBundle X := ⟨tensorObj N.obj (tensorPow H.obj (c x)),
    N.property.tensor pullbackTensorComparisonIsIso (tensorPow_isLocallyFreeRankOne X H (c x))⟩
  have hbc : b - c x + c x = b := Nat.sub_add_cancel hcb.le
  let e : P.obj ≅ tensorObj A.obj M.obj :=
    eP ≪≫ (tensorFunctor X).mapIso ((Iso.refl N.obj).prod
        (eqToIso (congrArg (tensorPow H.obj) hbc.symm) ≪≫
          (tensorPowAddIso H.obj (b - c x) (c x)).symm)) ≪≫
      (tensorAssociator N.obj (tensorPow H.obj (b - c x)) (tensorPow H.obj (c x))).symm ≪≫
      (tensorFunctor X).mapIso
        ((tensorComm N.obj (tensorPow H.obj (b - c x))).prod (Iso.refl _)) ≪≫
      tensorAssociator (tensorPow H.obj (b - c x)) N.obj (tensorPow H.obj (c x))
  exact exists_affine_section_of_ample_tensor A M P e hA (t x) hyx

end Langlands.AlgebraicGeometry.Picard
