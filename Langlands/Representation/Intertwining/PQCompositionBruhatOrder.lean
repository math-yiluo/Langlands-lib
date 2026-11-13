import Langlands.Representation.Intertwining.PQCompositionRegularityReduction
import Langlands.Representation.Intertwining.PQCompositionProductDecomposition
import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentIntersectionProduct
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Renard VII.3.5 (i): the Bruhat-order part of the regularity argument -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter Pointwise
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

section AbstractBruhat

variable {Γ : Type*} [Group Γ]

/-- The identity double coset `P · 1 · Q` is the product set `P Q`. -/
theorem quotToDoubleCoset_mk_one (P Q : Subgroup Γ) :
    DoubleCoset.quotToDoubleCoset P Q (DoubleCoset.mk P Q 1) = (P : Set Γ) * Q := by
  ext x
  rw [DoubleCoset.mem_quotToDoubleCoset_iff, eq_comm, DoubleCoset.eq, Set.mem_mul]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, by rw [mul_one]⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, by rw [mul_one]⟩

/-- `PzQ` is the identity double coset exactly when `z ∈ P Q`. -/
theorem mk_eq_mk_one_iff (P Q : Subgroup Γ) (z : Γ) :
    DoubleCoset.mk P Q z = DoubleCoset.mk P Q 1 ↔ z ∈ (P : Set Γ) * Q := by
  rw [← quotToDoubleCoset_mk_one, DoubleCoset.mem_quotToDoubleCoset_iff]

/-- If `P₂ ⊆ P₁ P₃` then `P₂ P₃ ⊆ P₁ P₃` and `P₁ P₂ ⊆ P₁ P₃`. -/
theorem mul_subset_of_subset_mul {P₁ P₂ P₃ : Subgroup Γ}
    (h : (P₂ : Set Γ) ⊆ (P₁ : Set Γ) * P₃) :
    (P₂ : Set Γ) * P₃ ⊆ (P₁ : Set Γ) * P₃ ∧ (P₁ : Set Γ) * P₂ ⊆ (P₁ : Set Γ) * P₃ := by
  constructor
  · rintro x ⟨a, ha, b, hb, rfl⟩
    obtain ⟨c, hc, d, hd, rfl⟩ := h ha
    exact ⟨c, hc, d * b, P₃.mul_mem hd hb, by simp only [mul_assoc]⟩
  · rintro x ⟨a, ha, b, hb, rfl⟩
    obtain ⟨c, hc, d, hd, rfl⟩ := h hb
    exact ⟨a * c, P₁.mul_mem ha hc, d, hd, by simp only [mul_assoc]⟩

/-- An element `v` of a subgroup `N` normalized by `x` commutes with `x` when the commutator
`x⁻¹ (v⁻¹ x v)`, which lies in `N`, is forced to be trivial. -/
theorem commute_of_commutator_eq_one {N : Subgroup Γ} {x v : Γ}
    (hx : x ∈ Subgroup.normalizer (N : Set Γ)) (hv : v ∈ N)
    (htriv : x⁻¹ * (v⁻¹ * x * v) ∈ N → x⁻¹ * (v⁻¹ * x * v) = 1) : Commute v x := by
  have hxi : x⁻¹ ∈ Subgroup.normalizer (N : Set Γ) := Subgroup.inv_mem _ hx
  have h1 : x⁻¹ * v⁻¹ * x⁻¹⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp hxi v⁻¹).mp (N.inv_mem hv)
  rw [inv_inv] at h1
  have h2 : x⁻¹ * (v⁻¹ * x * v) ∈ N := by
    have := N.mul_mem h1 hv
    simpa only [mul_assoc] using this
  have h3 := inv_mul_eq_one.mp (htriv h2)
  calc v * x = v * (v⁻¹ * x * v) := by rw [← h3]
    _ = x * v := by group

/-- In a semidirect decomposition `P = M ⋉ U`, the subgroups `M` and `U` meet trivially. -/
theorem _root_.Langlands.Aubert.General.IsSemidirectDecomposition.eq_one_of_mem_levi_of_mem_radical
    {P M U : Subgroup Γ}
    (h : IsSemidirectDecomposition P M U) {x : Γ} (hM : x ∈ M) (hU : x ∈ U) : x = 1 := by
  have h1 := h.projection_levi ⟨x, hM⟩
  have h2 := (h.projection_eq_one_iff ⟨x, h.levi_le hM⟩).mpr hU
  rw [h1] at h2
  exact congrArg Subtype.val h2

/-- In a semidirect decomposition `P = M ⋉ U`, every element of `P` is `m u` with `m ∈ M` and
`u ∈ U`. -/
theorem _root_.Langlands.Aubert.General.IsSemidirectDecomposition.exists_mul_eq
    {P M U : Subgroup Γ}
    (h : IsSemidirectDecomposition P M U) {x : Γ} (hx : x ∈ P) :
    ∃ m ∈ M, ∃ u ∈ U, x = m * u := by
  refine ⟨(h.projection ⟨x, hx⟩ : Γ), (h.projection ⟨x, hx⟩).2,
    ((h.projection ⟨x, hx⟩ : M) : Γ)⁻¹ * x, h.projection_inv_mul_mem ⟨x, hx⟩, ?_⟩
  group

variable [TopologicalSpace Γ] [ContinuousMul Γ]

/-- `PzQ ≤_{PQ} PQ` exactly when `z` lies in the closure of `P Q`. -/
theorem bruhatLE_mk_one_iff (P Q : Subgroup Γ) (z : Γ) :
    Geometric.BruhatLE P Q (DoubleCoset.mk P Q z) (DoubleCoset.mk P Q 1) ↔
      z ∈ closure ((P : Set Γ) * (Q : Set Γ)) := by
  unfold Geometric.BruhatLE
  rw [quotToDoubleCoset_mk_one]
  constructor
  · intro h
    exact h ((DoubleCoset.mem_quotToDoubleCoset_iff _ _).mpr rfl)
  · intro hz x hx
    rw [DoubleCoset.mem_quotToDoubleCoset_iff, eq_comm, DoubleCoset.eq] at hx
    obtain ⟨p, hp, q, hq, rfl⟩ := hx
    have hcont : Continuous fun y : Γ => p * y * q :=
      (continuous_const.mul continuous_id).mul continuous_const
    refine map_mem_closure (f := fun y : Γ => p * y * q) hcont hz ?_
    rintro y ⟨a, ha, b, hb, rfl⟩
    exact ⟨p * a, P.mul_mem hp ha, b * q, Q.mul_mem hb hq, by simp only [mul_assoc]⟩

/-- The Bruhat-order transfer of Renard VII.3.5 (i) for abstract subgroups: if `P₂ ⊆ P₁ P₃`,
`M ≤ P₁ ∩ P₂`, and every `z ∈ P₁ P₃` under consideration lies in `M`, then strict predecessors
of the identity for `(P₂, P₃)` and for `(P₁, P₂)` are strict predecessors for `(P₁, P₃)`. -/
theorem bruhatLT_mk_one_of_subset_mul {P₁ P₂ P₃ M : Subgroup Γ}
    (h : (P₂ : Set Γ) ⊆ (P₁ : Set Γ) * P₃) (hM₁ : M ≤ P₁) (hM₂ : M ≤ P₂) {z : Γ}
    (hcore : z ∈ (P₁ : Set Γ) * P₃ → z ∈ M) :
    (Geometric.BruhatLT P₂ P₃ (DoubleCoset.mk P₂ P₃ z) (DoubleCoset.mk P₂ P₃ 1) →
        Geometric.BruhatLT P₁ P₃ (DoubleCoset.mk P₁ P₃ z) (DoubleCoset.mk P₁ P₃ 1)) ∧
      (Geometric.BruhatLT P₁ P₂ (DoubleCoset.mk P₁ P₂ z) (DoubleCoset.mk P₁ P₂ 1) →
        Geometric.BruhatLT P₁ P₃ (DoubleCoset.mk P₁ P₃ z) (DoubleCoset.mk P₁ P₃ 1)) := by
  obtain ⟨h23, h12⟩ := mul_subset_of_subset_mul h
  constructor
  · rintro ⟨hle, hne⟩
    refine ⟨(bruhatLE_mk_one_iff P₁ P₃ z).mpr
      (closure_mono h23 ((bruhatLE_mk_one_iff P₂ P₃ z).mp hle)), fun heq => hne ?_⟩
    rw [mk_eq_mk_one_iff] at heq ⊢
    exact ⟨z, hM₂ (hcore heq), 1, P₃.one_mem, mul_one z⟩
  · rintro ⟨hle, hne⟩
    refine ⟨(bruhatLE_mk_one_iff P₁ P₃ z).mpr
      (closure_mono h12 ((bruhatLE_mk_one_iff P₁ P₂ z).mp hle)), fun heq => hne ?_⟩
    rw [mk_eq_mk_one_iff] at heq ⊢
    exact ⟨z, hM₁ (hcore heq), 1, P₂.one_mem, mul_one z⟩

end AbstractBruhat

open GroupScheme

section Contraction

open BruhatTits.DynamicUnipotentContainment AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]

/-- A rational point of the dynamic unipotent radical `U(χ)(F)` commuting with every value of
`χ` is trivial: conjugation by the powers of a contracting value of `χ` sends it to `1`. -/
theorem eq_one_of_mem_unipotentPoints_of_commute
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) {u : RationalPoint F G.X}
    (hu : u ∈ unipotentPoints χ) (hc : ∀ t : Fˣ, Commute u (cocharPoint χ t)) : u = 1 := by
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  have : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
  obtain ⟨t, ht⟩ := exists_unit_tendsto_pow_zero (F := F)
  have h := (tendsto_cocharPoint_pow_conj χ t ht ⟨u, hu⟩).comp
    (tendsto_id.prodMk (tendsto_const_nhds (x := (⟨u, hu⟩ : unipotentPoints χ))))
  have hconst : ∀ n : ℕ, cocharPoint χ t ^ n * u * (cocharPoint χ t ^ n)⁻¹ = u := by
    intro n
    rw [((hc t).pow_right n).eq.symm, mul_inv_cancel_right]
  have h' : Tendsto (fun _ : ℕ => u) atTop (𝓝 1) := by
    refine h.congr fun n => ?_
    exact hconst n
  exact tendsto_nhds_unique tendsto_const_nhds h'

end Contraction

section Core

open BruhatTits.DynamicUnipotentContainment

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- If a maximal split torus `T` of `G` lies in `M` and in `zMz⁻¹`, then for every cocharacter
`ν` of a central split torus `a : A ⟶ M`, `z⁻¹ ν(s) z ∈ M(F)`. -/
theorem conj_cocharPoint_mem_of_torus {M : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom M.X.hom] {m₀ : M ⟶ G} (hm₀ : IsClosedSubgroup m₀)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsCentralSplitTorus a) {z : rationalPoints G}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ta : T.toGrp ⟶ M} (hta : ta ≫ m₀ = i)
    {tb : T.toGrp ⟶ M} (htb : tb ≫ m₀ ≫ (G.innerIso z).hom = i)
    (ν : cocharacterLattice A) (s : kˣ) :
    z⁻¹ * cocharPoint (CommGroupScheme.groupHom ν ≫ a ≫ m₀) s * z ∈ pointImage m₀ := by
  obtain ⟨g, hg⟩ := ha.exists_factor_of_isMaximalSplitTorus hm₀ (t := ta) (by rw [hta]; exact hi)
  have key : CommGroupScheme.groupHom ν ≫ a ≫ m₀ =
      (CommGroupScheme.groupHom ν ≫ g ≫ tb) ≫ m₀ ≫ (G.innerIso z).hom := by
    rw [← hg, Category.assoc, Category.assoc, hta, ← htb]
    simp only [Category.assoc]
  let y := rationalPoints.map (CommGroupScheme.groupHom ν ≫ g ≫ tb)
    (MatrixRepresentation.gmRationalPoint s)
  have e : cocharPoint (CommGroupScheme.groupHom ν ≫ a ≫ m₀) s =
      rationalPoints.map (G.innerIso z).hom (rationalPoints.map m₀ y) := by
    rw [MatrixRepresentation.cocharPoint_eq_gmRationalPoint_comp, key]
    simp only [y, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  refine ⟨y, ?_⟩
  rw [e, rationalPoints_map_innerIso]
  change _ = z⁻¹ * (z * rationalPoints.map m₀ y * z⁻¹) * z
  group

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom]

omit [T2Space k] in
/-- The chart `U(χ)(F) = (U(ψ) ∩ U(χ))(F) · (U(ψ⁻¹) ∩ U(χ))(F)` for two cocharacters with the same
centralizer, as a factorization of each point. -/
theorem exists_mul_eq_of_secondChart [Smooth G.X.hom]
    {χ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
    (hZ : (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) =
      (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _)))
    {n : rationalPoints G} (hn : n ∈ unipotentPoints χ) :
    ∃ b ∈ unipotentPoints ψ,
      ∃ c ∈ unipotentPoints (Dynamic.inverseCocharacter ψ) ⊓ unipotentPoints χ, n = b * c := by
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  let e := Plancherel.StandardIntertwining.OppositeCharts.secondChart hZ
  refine ⟨(e.symm ⟨n, hn⟩).1.val.val, Subgroup.mem_subgroupOf.mp (e.symm ⟨n, hn⟩).1.prop,
    (e.symm ⟨n, hn⟩).2.val, (e.symm ⟨n, hn⟩).2.prop, ?_⟩
  exact (congrArg Subtype.val (e.apply_symm_apply ⟨n, hn⟩)).symm

set_option maxHeartbeats 1000000 in
/-- The core of the strictness part of Renard VII.3.5 (i): a point `z ∈ P₁(F) P₃(F)` such that
`M ∩ zMz⁻¹` contains a maximal split torus of `G` lies in `M(F)`. Write `z = v w` with
`v ∈ N̄₃(F)` and `w ∈ P₃(F)`; `v` commutes with the values of a cocharacter of the split
component contracting `N̄₃`, so `v = 1`; then `w = m u` with `u ∈ N₃(F)`, and `u` commutes
with the values of a cocharacter contracting `N₃`, so `u = 1`. -/
theorem mem_levi_of_mem_mul_of_torus (hG : IsConnectedReductive G)
    {M P₁ N₁ P₃ N₃ Pb₁ Nb₁ Pb₃ Nb₃ : GroupScheme (Spec (CommRingCat.of k))}
    {p₁ : P₁ ⟶ G} {l₁ : M ⟶ P₁} {r₁ : N₁ ⟶ P₁} (hp₁ : IsParabolicSubgroup p₁)
    (hl₁ : IsRationalLeviSubgroup l₁) (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
    (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
    {p₃ : P₃ ⟶ G} {l₃ : M ⟶ P₃} {r₃ : N₃ ⟶ P₃} (hp₃ : IsParabolicSubgroup p₃)
    (hl₃ : IsRationalLeviSubgroup l₃) (hr₃ : LeviSubgroup.IsGeometricUnipotentRadical r₃)
    (hmul₃ : IsIso (subgroupMultiplication l₃ r₃))
    {pb₁ : Pb₁ ⟶ G} {lb₁ : M ⟶ Pb₁} {rb₁ : Nb₁ ⟶ Pb₁} (hpb₁ : IsParabolicSubgroup pb₁)
    (hlb₁ : IsRationalLeviSubgroup lb₁) (hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
    {pb₃ : Pb₃ ⟶ G} {lb₃ : M ⟶ Pb₃} {rb₃ : Nb₃ ⟶ Pb₃} (hpb₃ : IsParabolicSubgroup pb₃)
    (hlb₃ : IsRationalLeviSubgroup lb₃) (hrb₃ : LeviSubgroup.IsGeometricUnipotentRadical rb₃)
    (hmulb₃ : IsIso (subgroupMultiplication lb₃ rb₃))
    (h31 : l₃ ≫ p₃ = l₁ ≫ p₁) (hb1 : lb₁ ≫ pb₁ = l₁ ≫ p₁) (hb3 : lb₃ ≫ pb₃ = l₁ ≫ p₁)
    (ho1 : pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁))
    (ho3 : pointImage p₃ ⊓ pointImage pb₃ = pointImage (l₁ ≫ p₁))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M} (ha : IsSplitComponent a)
    {z : rationalPoints G} {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ta : T.toGrp ⟶ M} (hta : ta ≫ l₁ ≫ p₁ = i)
    {tb : T.toGrp ⟶ M} (htb : tb ≫ l₁ ≫ p₁ ≫ (G.innerIso z).hom = i)
    (hz : z ∈ (pointImage p₁ : Set (rationalPoints G)) * (pointImage p₃ : Set _)) :
    z ∈ pointImage (l₁ ≫ p₁) := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom M.X.hom := hl₁.isConnectedReductive.isAffineHom
  have hm₀ : IsClosedSubgroup (l₁ ≫ p₁) := hl₁.isClosedSubgroup.comp hp₁.isClosedSubgroup
  have hconj := conj_cocharPoint_mem_of_torus hm₀ ha.isCentralSplitTorus hi hta htb
  obtain ⟨lam₁, -, -, hN₁, -, hZ₁, -⟩ :=
    exists_oppositePair_cocharacter hG ha hp₁ hl₁ hr₁ hpb₁ hlb₁ hrb₁ rfl hb1 ho1
  obtain ⟨lam₃, -, -, hN₃, -, hZ₃, -⟩ :=
    exists_oppositePair_cocharacter hG ha hp₃ hl₃ hr₃ hpb₃ hlb₃ hrb₃ h31 hb3 ho3
  obtain ⟨lamb, -, -, hNb, hNb', hZb, -⟩ :=
    exists_oppositePair_cocharacter hG ha hpb₃ hlb₃ hrb₃ hp₃ hl₃ hr₃ hb3 h31
      (by rw [inf_comm]; exact ho3)
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hd₁ : IsSemidirectDecomposition (pointImage p₁) (pointImage (l₁ ≫ p₁))
      (pointImage (r₁ ≫ p₁)) :=
    isSemidirectDecomposition_pointImage p₁ l₁ r₁ hp₁.isClosedSubgroup hr₁ hmul₁
  have hd₃ : IsSemidirectDecomposition (pointImage p₃) (pointImage (l₁ ≫ p₁))
      (pointImage (r₃ ≫ p₃)) := by
    rw [← h31]
    exact isSemidirectDecomposition_pointImage p₃ l₃ r₃ hp₃.isClosedSubgroup hr₃ hmul₃
  have hdb₃ : IsSemidirectDecomposition (pointImage pb₃) (pointImage (l₁ ≫ p₁))
      (pointImage (rb₃ ≫ pb₃)) := by
    rw [← hb3]
    exact isSemidirectDecomposition_pointImage pb₃ lb₃ rb₃ hpb₃.isClosedSubgroup hrb₃ hmulb₃
  have hcocb : ∀ s : kˣ,
      cocharPoint (CommGroupScheme.groupHom lamb ≫ a ≫ l₁ ≫ p₁) s ∈ pointImage (l₁ ≫ p₁) := by
    intro s
    rw [pointImage_eq_range_carrier, hZb]
    exact cocharPoint_mem_centralizer _ s
  have hcoc₃ : ∀ s : kˣ,
      cocharPoint (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁) s ∈ pointImage (l₁ ≫ p₁) := by
    intro s
    rw [pointImage_eq_range_carrier, hZ₃]
    exact cocharPoint_mem_centralizer _ s
  -- Step 2: a point `w = m' u` of `P₃(F)` with the torus property lies in `M(F)`.
  have step₂ : ∀ w ∈ pointImage p₃, (∀ s : kˣ,
      w⁻¹ * cocharPoint (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁) s * w ∈
        pointImage (l₁ ≫ p₁)) → w ∈ pointImage (l₁ ≫ p₁) := by
    intro w hw hwc
    obtain ⟨m', hm', u, hu, rfl⟩ := hd₃.exists_mul_eq hw
    have hu1 : u = 1 := by
      apply eq_one_of_mem_unipotentPoints_of_commute
        (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁) (by rw [hN₃] at hu; exact hu)
      intro s
      refine commute_of_commutator_eq_one (N := pointImage (r₃ ≫ p₃))
        (hd₃.levi_le_normalizer (hcoc₃ s)) hu fun hmem => ?_
      have hcomm : Commute m' (cocharPoint (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁) s) :=
        commute_cocharPoint _ (by rw [← hZ₃]; exact hm') s
      have hx' : m'⁻¹ * cocharPoint (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁) s * m' =
          cocharPoint (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁) s := by
        rw [mul_assoc, ← hcomm.eq, inv_mul_cancel_left]
      have heq : u⁻¹ * cocharPoint (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁) s * u =
          (m' * u)⁻¹ * cocharPoint (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁) s *
            (m' * u) := by
        rw [show (m' * u)⁻¹ * cocharPoint (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁) s *
            (m' * u) = u⁻¹ * (m'⁻¹ * cocharPoint (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁) s *
              m') * u by group, hx']
      have hM : (cocharPoint (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁) s)⁻¹ *
          (u⁻¹ * cocharPoint (CommGroupScheme.groupHom lam₃ ≫ a ≫ l₁ ≫ p₁) s * u) ∈
            pointImage (l₁ ≫ p₁) := by
        rw [heq]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hcoc₃ s)) (hwc s)
      exact hd₃.eq_one_of_mem_levi_of_mem_radical hM hmem
    rw [hu1, mul_one]
    exact hm'
  -- Step 1: a point `v w` with `v ∈ N̄₃(F)`, `w ∈ P₃(F)` and the torus property has `v = 1`.
  have step₁ : ∀ v ∈ pointImage (rb₃ ≫ pb₃), ∀ w ∈ pointImage p₃, (∀ s : kˣ,
      (v * w)⁻¹ * cocharPoint (CommGroupScheme.groupHom lamb ≫ a ≫ l₁ ≫ p₁) s * (v * w) ∈
        pointImage (l₁ ≫ p₁)) → v = 1 := by
    intro v hv w hw hvw
    apply eq_one_of_mem_unipotentPoints_of_commute
      (CommGroupScheme.groupHom lamb ≫ a ≫ l₁ ≫ p₁) (by rw [hNb] at hv; exact hv)
    intro s
    refine commute_of_commutator_eq_one (N := pointImage (rb₃ ≫ pb₃))
      (hdb₃.levi_le_normalizer (hcocb s)) hv fun hmem => ?_
    have hP : (cocharPoint (CommGroupScheme.groupHom lamb ≫ a ≫ l₁ ≫ p₁) s)⁻¹ *
        (v⁻¹ * cocharPoint (CommGroupScheme.groupHom lamb ≫ a ≫ l₁ ≫ p₁) s * v) ∈
          pointImage p₃ := by
      have heq : v⁻¹ * cocharPoint (CommGroupScheme.groupHom lamb ≫ a ≫ l₁ ≫ p₁) s * v =
          w * ((v * w)⁻¹ * cocharPoint (CommGroupScheme.groupHom lamb ≫ a ≫ l₁ ≫ p₁) s *
            (v * w)) * w⁻¹ := by
        group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hd₃.levi_le (hcocb s)))
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (hd₃.levi_le (hvw s)))
          (Subgroup.inv_mem _ hw))
    have hM : (cocharPoint (CommGroupScheme.groupHom lamb ≫ a ≫ l₁ ≫ p₁) s)⁻¹ *
        (v⁻¹ * cocharPoint (CommGroupScheme.groupHom lamb ≫ a ≫ l₁ ≫ p₁) s * v) ∈
          pointImage (l₁ ≫ p₁) := by
      rw [← ho3]
      exact ⟨hP, hdb₃.unipotent_le hmem⟩
    exact hdb₃.eq_one_of_mem_levi_of_mem_radical hM hmem
  -- `z = m n y` with `m ∈ M(F)`, `n = b c ∈ N₁(F)`, `b ∈ N̄₃(F)`, `c ∈ N₃(F)`, `y ∈ P₃(F)`.
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  beta_reduce at hconj ⊢
  obtain ⟨m, hm, n, hn, rfl⟩ := hd₁.exists_mul_eq hx
  have hZ : (Dynamic.centralizer (CommGroupScheme.groupHom lam₁ ≫ a ≫ l₁ ≫ p₁)).carrier
        (Over.mk (𝟙 _)) =
      (Dynamic.centralizer (CommGroupScheme.groupHom lamb ≫ a ≫ l₁ ≫ p₁)).carrier
        (Over.mk (𝟙 _)) := by
    rw [← hZ₁, ← hZb]
  rw [hN₁] at hn
  obtain ⟨b, hb, c, hc, rfl⟩ := exists_mul_eq_of_secondChart hZ hn
  have hb' : b ∈ pointImage (rb₃ ≫ pb₃) := by
    rw [hNb]
    exact hb
  have hc' : c ∈ pointImage (r₃ ≫ p₃) := by
    rw [hNb', groupHom_neg_comp_eq_oppositeCocharacter]
    exact (Subgroup.mem_inf.mp hc).1
  have hv : m * b * m⁻¹ ∈ pointImage (rb₃ ≫ pb₃) :=
    (Subgroup.mem_normalizer_iff.mp (hdb₃.levi_le_normalizer hm) b).mp hb'
  have hw : m * c * y ∈ pointImage p₃ :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hd₃.levi_le hm) (hd₃.unipotent_le hc')) hy
  have hzvw : m * (b * c) * y = m * b * m⁻¹ * (m * c * y) := by group
  rw [hzvw] at hconj ⊢
  have hv1 := step₁ _ hv _ hw (hconj lamb)
  rw [hv1, one_mul] at hconj ⊢
  exact step₂ _ hw (hconj lam₃)

end Core

end Langlands.Aubert.General.RepresentedParabolic
