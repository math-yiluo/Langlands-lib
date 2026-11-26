import Langlands.Representation.Plancherel.RationalSourceGammaOpposite
import Langlands.Representation.Plancherel.CommonLeviCompactSplitting
import Langlands.Representation.Plancherel.SourceGammaIndexProduct

/-! # The actual source gamma across one wall of a common Levi -/

noncomputable section

namespace Langlands.Plancherel.SourceGammaIndexProduct

universe v

variable {A : Type v} [Group A]

/-- Membership of a Levi-first product in a subgroup with a unique ordered
factorization `H = (H ∩ U) (H ∩ M) (H ∩ V)`. -/
theorem mem_iff_of_unique_factorization {M U V H : Subgroup A}
    (hMU : M ≤ Subgroup.normalizer (U : Set A))
    (hunique : ∀ u ∈ U, ∀ m ∈ M, ∀ v ∈ V,
      ∀ u' ∈ U, ∀ m' ∈ M, ∀ v' ∈ V,
        u * m * v = u' * m' * v' → u = u' ∧ m = m' ∧ v = v')
    (hfactor : ∀ h ∈ H, ∃ u ∈ H ⊓ U, ∃ m ∈ H ⊓ M,
      ∃ v ∈ H ⊓ V, h = u * m * v)
    (m : M) (u : U) (v : V) :
    (m : A) * u * (v : A) ∈ H ↔
      (m : A) ∈ H ∧ (u : A) ∈ H ∧ (v : A) ∈ H := by
  constructor
  · intro hh
    let u' : U := ⟨(m : A) * u * (m : A)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hMU m.property) (u : A)).mp u.property⟩
    obtain ⟨a, ha, b, hb, c, hc, he⟩ := hfactor _ hh
    have heq : (u' : A) * m * (v : A) = a * b * c := by
      calc
        _ = (m : A) * u * (v : A) := by dsimp [u']; group
        _ = _ := he
    obtain ⟨hua, hmb, hvc⟩ := hunique u' u'.property m m.property v v.property
      a ha.2 b hb.2 c hc.2 heq
    have hmH : (m : A) ∈ H := hmb.symm ▸ hb.1
    have huH' : (u' : A) ∈ H := hua.symm ▸ ha.1
    have huH : (u : A) ∈ H := by
      have hh' := H.mul_mem (H.mul_mem (H.inv_mem hmH) huH') hmH
      simpa [u', mul_assoc] using hh'
    exact ⟨hmH, huH, hvc.symm ▸ hc.1⟩
  · rintro ⟨hm, hu, hv⟩
    exact H.mul_mem (H.mul_mem hm hu) hv

end Langlands.Plancherel.SourceGammaIndexProduct

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz SourceGammaIndexProduct
open BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance sourceGammaWallPointTopology : TopologicalSpace (RationalPoint F G.X) :=
  rationalPointTopology F G.X
local instance sourceGammaWallPointMeasurable : MeasurableSpace (RationalPoint F G.X) :=
  borel (RationalPoint F G.X)
local instance sourceGammaWallPointBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance sourceGammaWallFieldT2 : T2Space F := BruhatTits.localField_t2Space F
local instance sourceGammaWallPointTopologicalGroup :
    IsTopologicalGroup (RationalPoint F G.X) := rationalPoint_isTopologicalGroup F G
local instance sourceGammaWallPointT2 : T2Space (RationalPoint F G.X) :=
  rationalPoint_t2Space F G
local instance sourceGammaWallPointLocallyCompact : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance sourceGammaWallPointNonarchimedean : NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
local instance sourceGammaWallFieldSecondCountable : SecondCountableTopology F :=
  localField_secondCountableTopology F
local instance sourceGammaWallPointSecondCountable :
    SecondCountableTopology (RationalPoint F G.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F G
local instance subgroupSecondCountableGammaWall (H : Subgroup (RationalPoint F G.X)) :
    SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set (RationalPoint F G.X))

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))

section Limit

variable (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) [IsSeparated G.X.hom]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] [IsAffine G.X.left] in
/-- Every rational point of `P(ψ)` is its dynamic limit times a point of `U(ψ)`. -/
theorem exists_limit_mul_unipotent {x : RationalPoint F G.X}
    (hx : x ∈ (Dynamic.parabolic ψ).carrier X₀) :
    ∃ n ∈ unipotentPoints ψ,
      x = (Dynamic.limitHom ψ X₀ ⟨x, hx⟩ : RationalPoint F G.X) * n := by
  have h := (dynamic_isSemidirectDecomposition ψ X₀).projection_inv_mul_mem ⟨x, hx⟩
  rw [dynamic_projection_eq_limitHom] at h
  exact ⟨_, h, by group⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] [IsAffine G.X.left] in
/-- A limit-stable subgroup has split traces on every subgroup of `P(ψ)` containing
`U(ψ)`. -/
theorem splitTrace_of_limit_stable {Y X : Subgroup (RationalPoint F G.X)}
    (hY : ∀ p : (Dynamic.parabolic ψ).carrier X₀, (p : RationalPoint F G.X) ∈ Y →
      (Dynamic.limitHom ψ X₀ p : RationalPoint F G.X) ∈ Y)
    (hXP : X ≤ (Dynamic.parabolic ψ).carrier X₀) (hNX : unipotentPoints ψ ≤ X) :
    SplitTrace Y X ((Dynamic.centralizer ψ).carrier X₀) (unipotentPoints ψ) := by
  intro x hx
  obtain ⟨hxY, hxX⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨n, hn, e⟩ := exists_limit_mul_unipotent ψ (hXP hxX)
  set l := (Dynamic.limitHom ψ X₀ ⟨x, hXP hxX⟩ : RationalPoint F G.X)
  have hlY : l ∈ Y := hY ⟨x, hXP hxX⟩ hxY
  have hlX : l = x * n⁻¹ := by rw [e]; group
  refine ⟨l, Subgroup.mem_inf.mpr ⟨hlY, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩, n, ?_, e⟩
  · rw [hlX]
    exact X.mul_mem hxX (X.inv_mem (hNX hn))
  · exact (Dynamic.limitHom ψ X₀ ⟨x, hXP hxX⟩).2
  · refine Subgroup.mem_inf.mpr ⟨?_, hn⟩
    have : n = l⁻¹ * x := by rw [e]; group
    rw [this]
    exact Y.mul_mem (Y.inv_mem hlY) hxY

end Limit

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Traces of compact open subgroups on actual subgroups are relative indices of
intersections. -/
theorem sourceTraceIndex_eq_relIndex (K H : OpenSubgroup (RationalPoint F G.X))
    (X : Subgroup (RationalPoint F G.X)) :
    sourceTraceIndex K H X = (H.toSubgroup ⊓ X).relIndex (K.toSubgroup ⊓ X) := by
  unfold sourceTraceIndex
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq, Subgroup.range_subtype,
    inf_comm X]
  apply relIndex_congr_inf
  ext x
  simp only [Subgroup.mem_inf]
  tauto

/-- **Source gamma across one wall.** Let `χ` and `χ'` have the same actual Levi points
`M`, and let `φ` have Levi points `L ⊇ M`, with `U(φ) ≤ U(χ) ∩ U(χ')`,
`U(φ⁻¹) ≤ U(χ⁻¹) ∩ U(χ'⁻¹)`, the radicals of `χ, χ'` in `P(φ)` and those of
`χ⁻¹, χ'⁻¹` in `P(φ⁻¹)`, and with `U(χ) ∩ L = U(χ'⁻¹) ∩ L` and
`U(χ⁻¹) ∩ L = U(χ') ∩ L`. If the common compact is limit-stable for `χ`, `χ'`,
`φ` and `φ⁻¹`, the two actual source gammas agree. The wall is the face of `φ`; it may
lie on several root hyperplanes. -/
theorem gamma_eq_of_wall (hG : IsConnectedReductive G)
    (χ χ' φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hM : (Dynamic.centralizer χ').carrier X₀ = (Dynamic.centralizer χ).carrier X₀)
    (hML : (Dynamic.centralizer χ).carrier X₀ ≤ (Dynamic.centralizer φ).carrier X₀)
    (hNU : unipotentPoints φ ≤ unipotentPoints χ)
    (hNU' : unipotentPoints φ ≤ unipotentPoints χ')
    (hNV : unipotentPoints (oppositeCocharacter φ) ≤ unipotentPoints (oppositeCocharacter χ))
    (hNV' : unipotentPoints (oppositeCocharacter φ) ≤
      unipotentPoints (oppositeCocharacter χ'))
    (hUP : unipotentPoints χ ≤ (Dynamic.parabolic φ).carrier X₀)
    (hUP' : unipotentPoints χ' ≤ (Dynamic.parabolic φ).carrier X₀)
    (hVP : unipotentPoints (oppositeCocharacter χ) ≤
      (Dynamic.parabolic (oppositeCocharacter φ)).carrier X₀)
    (hVP' : unipotentPoints (oppositeCocharacter χ') ≤
      (Dynamic.parabolic (oppositeCocharacter φ)).carrier X₀)
    (hB : unipotentPoints χ ⊓ (Dynamic.centralizer φ).carrier X₀ =
      unipotentPoints (oppositeCocharacter χ') ⊓ (Dynamic.centralizer φ).carrier X₀)
    (hC : unipotentPoints (oppositeCocharacter χ) ⊓ (Dynamic.centralizer φ).carrier X₀ =
      unipotentPoints χ' ⊓ (Dynamic.centralizer φ).carrier X₀)
    (hstable : ∀ p : (Dynamic.parabolic χ).carrier X₀, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    (hstable' : ∀ p : (Dynamic.parabolic χ').carrier X₀, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ' X₀ p : RationalPoint F G.X) ∈ K)
    (hstableφ : ∀ p : (Dynamic.parabolic φ).carrier X₀, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom φ X₀ p : RationalPoint F G.X) ∈ K)
    (hstableφ' : ∀ p : (Dynamic.parabolic (oppositeCocharacter φ)).carrier X₀,
      (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom (oppositeCocharacter φ) X₀ p : RationalPoint F G.X) ∈ K) :
    gamma χ K hK = gamma χ' K hK := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsSeparated G.X.hom := hG.isSeparated
  let : Smooth G.X.hom := hG.smooth
  set M := (Dynamic.centralizer χ).carrier X₀ with hMdef
  set L := (Dynamic.centralizer φ).carrier X₀ with hLdef
  set N := unipotentPoints φ with hNdef
  set N' := unipotentPoints (oppositeCocharacter φ) with hN'def
  have hLopp : (Dynamic.centralizer (oppositeCocharacter φ)).carrier X₀ = L := by
    rw [show Dynamic.centralizer (oppositeCocharacter φ) = Dynamic.centralizer φ from
      Dynamic.centralizer_inverseCocharacter φ]
  have hLN : L ≤ Subgroup.normalizer (N : Set (RationalPoint F G.X)) :=
    Dynamic.centralizer_le_normalizer_unipotent φ X₀
  have hLN' : L ≤ Subgroup.normalizer (N' : Set (RationalPoint F G.X)) := by
    rw [← hLopp]
    exact Dynamic.centralizer_le_normalizer_unipotent (oppositeCocharacter φ) X₀
  -- the auxiliary subgroups
  obtain ⟨hH₁c, hH₁K, hH₁f, hH₁f'⟩ := gammaAuxiliarySubgroup_spec φ K hG
  set H₁ := gammaAuxiliarySubgroup φ K hG
  obtain ⟨g, hg, H, hHc, hHH₁, hHfac, hHU, n₀, hHV⟩ :=
    StandardIntertwining.CommonLeviSplitting.exists_iwahoriCut χ H₁ hH₁c
  have hHK : H ≤ K := fun x hx => hH₁K (hHH₁ hx)
  have hgL : ∀ j : ℕ, g ^ j ∈ L := fun j => pow_mem (hML hg) j
  have hgL' : g⁻¹ ∈ L := L.inv_mem (hML hg)
  -- the trace of `H` on `U(χ)` splits along `φ`
  have hHU1 : SplitTrace H.toSubgroup (unipotentPoints χ) L N := by
    intro x hx
    obtain ⟨hxH, hxU⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨n, hn, e⟩ := exists_limit_mul_unipotent φ (hUP hxU)
    set l := (Dynamic.limitHom φ X₀ ⟨x, hUP hxU⟩ : RationalPoint F G.X)
    have hlL : l ∈ L := (Dynamic.limitHom φ X₀ ⟨x, hUP hxU⟩).2
    have hlU : l ∈ unipotentPoints χ := by
      have : l = x * n⁻¹ := by rw [e]; group
      rw [this]
      exact Subgroup.mul_mem _ hxU (Subgroup.inv_mem _ (hNU hn))
    have hconj : ∀ j : ℕ, g ^ j * l * (g ^ j)⁻¹ ∈ H₁ ∧ g ^ j * n * (g ^ j)⁻¹ ∈ H₁ := by
      intro j
      have hx' := (hHU x hxU).mp hxH j
      have e' : g ^ j * x * (g ^ j)⁻¹ =
          (g ^ j * l * (g ^ j)⁻¹) * (g ^ j * n * (g ^ j)⁻¹) * 1 := by
        rw [e]; group
      rw [e'] at hx'
      have hl' : g ^ j * l * (g ^ j)⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem (hgL j) hlL) (L.inv_mem (hgL j))
      have hn' : g ^ j * n * (g ^ j)⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hLN (hgL j)) n).mp hn
      have h3 := (hH₁f ⟨_, hl'⟩ ⟨_, hn'⟩ 1).mp hx'
      exact ⟨h3.1, h3.2.1⟩
    refine ⟨l, Subgroup.mem_inf.mpr ⟨(hHU l hlU).mpr fun j => (hconj j).1,
      Subgroup.mem_inf.mpr ⟨hlU, hlL⟩⟩, n,
      Subgroup.mem_inf.mpr ⟨(hHU n (hNU hn)).mpr fun j => (hconj j).2, hn⟩, e⟩
  -- the trace of `H` on `U(χ⁻¹)` splits along `φ⁻¹`
  have hHV1 : SplitTrace H.toSubgroup (unipotentPoints (oppositeCocharacter χ)) L N' := by
    intro x hx
    obtain ⟨hxH, hxV⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨n, hn, e⟩ := exists_limit_mul_unipotent (oppositeCocharacter φ) (hVP hxV)
    set l := (Dynamic.limitHom (oppositeCocharacter φ) X₀ ⟨x, hVP hxV⟩ : RationalPoint F G.X)
    have hlL : l ∈ L := hLopp ▸ (Dynamic.limitHom (oppositeCocharacter φ) X₀ ⟨x, hVP hxV⟩).2
    have hlV : l ∈ unipotentPoints (oppositeCocharacter χ) := by
      have : l = x * n⁻¹ := by rw [e]; group
      rw [this]
      exact Subgroup.mul_mem _ hxV (Subgroup.inv_mem _ (hNV hn))
    have hcL : ∀ j : ℕ, g⁻¹ ^ j * g ^ n₀ ∈ L := fun j =>
      L.mul_mem (pow_mem hgL' j) (hgL n₀)
    have hconj : ∀ j : ℕ, (g⁻¹ ^ j * g ^ n₀) * l * (g⁻¹ ^ j * g ^ n₀)⁻¹ ∈ H₁ ∧
        (g⁻¹ ^ j * g ^ n₀) * n * (g⁻¹ ^ j * g ^ n₀)⁻¹ ∈ H₁ := by
      intro j
      have hx' := (hHV x hxV).mp hxH j
      set c := g⁻¹ ^ j * g ^ n₀
      have e' : c * x * c⁻¹ = (c * l * c⁻¹) * (c * n * c⁻¹) * 1 := by
        rw [e]; group
      rw [e'] at hx'
      have hl' : c * l * c⁻¹ ∈ L := L.mul_mem (L.mul_mem (hcL j) hlL) (L.inv_mem (hcL j))
      have hn' : c * n * c⁻¹ ∈ N' :=
        (Subgroup.mem_normalizer_iff.mp (hLN' (hcL j)) n).mp hn
      have h3 := (hH₁f' ⟨_, hl'⟩ ⟨_, hn'⟩ 1).mp hx'
      exact ⟨h3.1, h3.2.1⟩
    refine ⟨l, Subgroup.mem_inf.mpr ⟨(hHV l hlV).mpr fun j => (hconj j).1,
      Subgroup.mem_inf.mpr ⟨hlV, hlL⟩⟩, n,
      Subgroup.mem_inf.mpr ⟨(hHV n (hNV hn)).mpr fun j => (hconj j).2, hn⟩, e⟩
  -- uniqueness in the open cell of `φ`
  have hNLNu : ∀ n ∈ N, ∀ l ∈ L, ∀ n' ∈ N', ∀ m ∈ N, ∀ k ∈ L, ∀ m' ∈ N',
      n * l * n' = m * k * m' → n = m ∧ l = k ∧ n' = m' := by
    have huniq := RationalPointFamily.dynamic_opposite_factorization_unique
      (oppositeCocharacter φ)
    have hdouble : Dynamic.inverseCocharacter (oppositeCocharacter φ) = φ :=
      Dynamic.inverseCocharacter_inverseCocharacter φ
    have hMopp : Dynamic.centralizer (oppositeCocharacter φ) = Dynamic.centralizer φ :=
      Dynamic.centralizer_inverseCocharacter φ
    rw [hdouble, hMopp] at huniq
    exact huniq
  have hLN1 : ∀ l ∈ L, l ∈ N → l = 1 := fun l hl hlN =>
    (hNLNu l hlN 1 (one_mem _) 1 (one_mem _) 1 (one_mem _) l hl 1 (one_mem _)
      (by group)).1
  have hLN1' : ∀ l ∈ L, l ∈ N' → l = 1 := fun l hl hlN =>
    ((hNLNu 1 (one_mem _) l hl 1 (one_mem _) 1 (one_mem _) 1 (one_mem _) l hlN
      (by group)).2.1)
  -- the factorization of `H` in the open cell of `φ`, with a `χ`-factored Levi part
  have hHfac' : ∀ h ∈ H, ∃ n ∈ H.toSubgroup ⊓ N,
      ∃ b ∈ H.toSubgroup ⊓ (unipotentPoints χ ⊓ L), ∃ z ∈ H.toSubgroup ⊓ M,
      ∃ c ∈ H.toSubgroup ⊓ (unipotentPoints (oppositeCocharacter χ) ⊓ L),
      ∃ n' ∈ H.toSubgroup ⊓ N', h = n * (b * z * c) * n' := by
    intro h hh
    obtain ⟨o, ho, z, hz, w, hw, hoH, hwH, e⟩ := hHfac h⁻¹ (H.inv_mem hh)
    have hzH : z ∈ H := by
      have : z = o⁻¹ * h⁻¹ * w⁻¹ := by rw [e]; group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.inv_mem hoH) (H.inv_mem hh)) (H.inv_mem hwH)
    obtain ⟨b, hb, n, hn, eb⟩ := hHU1 w⁻¹
      (Subgroup.mem_inf.mpr ⟨H.inv_mem hwH, Subgroup.inv_mem _ hw⟩)
    obtain ⟨c, hc, n', hn', ec⟩ := hHV1 o⁻¹
      (Subgroup.mem_inf.mpr ⟨H.inv_mem hoH, Subgroup.inv_mem _ ho⟩)
    have hbH : b ∈ H := (Subgroup.mem_inf.mp hb).1
    have hbL : b ∈ L := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).2).2
    refine ⟨b * n * b⁻¹, Subgroup.mem_inf.mpr
      ⟨H.mul_mem (H.mul_mem hbH (Subgroup.mem_inf.mp hn).1) (H.inv_mem hbH),
        (Subgroup.mem_normalizer_iff.mp (hLN hbL) n).mp (Subgroup.mem_inf.mp hn).2⟩,
      b, hb, z⁻¹, Subgroup.mem_inf.mpr ⟨H.inv_mem hzH, Subgroup.inv_mem _ hz⟩, c, hc, n', hn', ?_⟩
    calc h = (o * z * w)⁻¹ := by rw [← e, inv_inv]
      _ = w⁻¹ * z⁻¹ * o⁻¹ := by group
      _ = _ := by rw [eb, ec]; group
  have hbzcL : ∀ b ∈ H.toSubgroup ⊓ (unipotentPoints χ ⊓ L), ∀ z ∈ H.toSubgroup ⊓ M,
      ∀ c ∈ H.toSubgroup ⊓ (unipotentPoints (oppositeCocharacter χ) ⊓ L), b * z * c ∈ L :=
    fun b hb z hz c hc => L.mul_mem (L.mul_mem (Subgroup.mem_inf.mp hb).2.2
      (hML (Subgroup.mem_inf.mp hz).2)) (Subgroup.mem_inf.mp hc).2.2
  have hbzcH : ∀ b ∈ H.toSubgroup ⊓ (unipotentPoints χ ⊓ L), ∀ z ∈ H.toSubgroup ⊓ M,
      ∀ c ∈ H.toSubgroup ⊓ (unipotentPoints (oppositeCocharacter χ) ⊓ L), b * z * c ∈ H :=
    fun b hb z hz c hc => H.mul_mem (H.mul_mem (Subgroup.mem_inf.mp hb).1
      (Subgroup.mem_inf.mp hz).1) (Subgroup.mem_inf.mp hc).1
  -- limit stability of `H` for `φ` and `φ⁻¹`
  have hHφ : ∀ p : (Dynamic.parabolic φ).carrier X₀, (p : RationalPoint F G.X) ∈ H →
      (Dynamic.limitHom φ X₀ p : RationalPoint F G.X) ∈ H := by
    rintro ⟨x, hxP⟩ hxH
    obtain ⟨n, hn, b, hb, z, hz, c, hc, n', hn', e⟩ := hHfac' x hxH
    obtain ⟨m, hm, e2⟩ := exists_limit_mul_unipotent φ hxP
    set l := (Dynamic.limitHom φ X₀ ⟨x, hxP⟩ : RationalPoint F G.X)
    have hl : l ∈ L := (Dynamic.limitHom φ X₀ ⟨x, hxP⟩).2
    have h3 := hNLNu n (Subgroup.mem_inf.mp hn).2 (b * z * c) (hbzcL b hb z hz c hc)
      n' (Subgroup.mem_inf.mp hn').2 (l * m * l⁻¹)
      ((Subgroup.mem_normalizer_iff.mp (hLN hl) m).mp hm) l hl 1 (one_mem _)
      (by rw [← e]; rw [e2]; group)
    change l ∈ H
    rw [← h3.2.1]
    exact hbzcH b hb z hz c hc
  have hHφ' : ∀ p : (Dynamic.parabolic (oppositeCocharacter φ)).carrier X₀,
      (p : RationalPoint F G.X) ∈ H →
      (Dynamic.limitHom (oppositeCocharacter φ) X₀ p : RationalPoint F G.X) ∈ H := by
    rintro ⟨x, hxP⟩ hxH
    obtain ⟨n, hn, b, hb, z, hz, c, hc, n', hn', e⟩ := hHfac' x hxH
    obtain ⟨m, hm, e2⟩ := exists_limit_mul_unipotent (oppositeCocharacter φ) hxP
    set l := (Dynamic.limitHom (oppositeCocharacter φ) X₀ ⟨x, hxP⟩ : RationalPoint F G.X)
    have hl : l ∈ L := hLopp ▸ (Dynamic.limitHom (oppositeCocharacter φ) X₀ ⟨x, hxP⟩).2
    have h3 := hNLNu n (Subgroup.mem_inf.mp hn).2 (b * z * c) (hbzcL b hb z hz c hc)
      n' (Subgroup.mem_inf.mp hn').2 1 (one_mem _) l hl m hm
      (by rw [← e]; rw [e2]; group)
    change l ∈ H
    rw [← h3.2.1]
    exact hbzcH b hb z hz c hc
  -- all eight split traces
  have hKU : SplitTrace K.toSubgroup (unipotentPoints χ) L N :=
    splitTrace_of_limit_stable φ hstableφ hUP hNU
  have hKU' : SplitTrace K.toSubgroup (unipotentPoints χ') L N :=
    splitTrace_of_limit_stable φ hstableφ hUP' hNU'
  have hKV : SplitTrace K.toSubgroup (unipotentPoints (oppositeCocharacter χ)) L N' := by
    have h := splitTrace_of_limit_stable (oppositeCocharacter φ) hstableφ' hVP hNV
    rwa [hLopp] at h
  have hKV' : SplitTrace K.toSubgroup (unipotentPoints (oppositeCocharacter χ')) L N' := by
    have h := splitTrace_of_limit_stable (oppositeCocharacter φ) hstableφ' hVP' hNV'
    rwa [hLopp] at h
  have hHU' : SplitTrace H.toSubgroup (unipotentPoints χ') L N :=
    splitTrace_of_limit_stable φ hHφ hUP' hNU'
  have hHV' : SplitTrace H.toSubgroup (unipotentPoints (oppositeCocharacter χ')) L N' := by
    have h := splitTrace_of_limit_stable (oppositeCocharacter φ) hHφ' hVP' hNV'
    rwa [hLopp] at h
  have hnN : ∀ {X : Subgroup (RationalPoint F G.X)}, X ≤ (Dynamic.parabolic φ).carrier X₀ →
      ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun hX x hx n hn =>
    (Subgroup.mem_normalizer_iff.mp (dynamic_parabolic_le_normalizer φ X₀ (hX hx)) n).mp hn
  have hnN' : ∀ {X : Subgroup (RationalPoint F G.X)},
      X ≤ (Dynamic.parabolic (oppositeCocharacter φ)).carrier X₀ →
      ∀ x ∈ X, ∀ n ∈ N', x * n * x⁻¹ ∈ N' := fun hX x hx n hn =>
    (Subgroup.mem_normalizer_iff.mp
      (dynamic_parabolic_le_normalizer (oppositeCocharacter φ) X₀ (hX hx)) n).mp hn
  have hidx := relIndex_mul_eq_of_wall hHK hNU hNU' hNV hNV' (hnN hUP) (hnN hUP')
    (hnN' hVP) (hnN' hVP') hLN1 hLN1' hB hC hKU hHU1 hKU' hHU' hKV hHV1 hKV' hHV'
  -- the local factorizations for `χ` and `χ'`
  have hfac : ∀ (m : M) (u : unipotentPoints χ) (v : unipotentPoints (oppositeCocharacter χ)),
      (m : RationalPoint F G.X) * u * (v : RationalPoint F G.X) ∈ H ↔
        (m : RationalPoint F G.X) ∈ H ∧ (u : RationalPoint F G.X) ∈ H ∧
          (v : RationalPoint F G.X) ∈ H := by
    have huniq := RationalPointFamily.dynamic_opposite_factorization_unique
      (oppositeCocharacter χ)
    have hdouble : Dynamic.inverseCocharacter (oppositeCocharacter χ) = χ :=
      Dynamic.inverseCocharacter_inverseCocharacter χ
    have hMopp : Dynamic.centralizer (oppositeCocharacter χ) = Dynamic.centralizer χ :=
      Dynamic.centralizer_inverseCocharacter χ
    rw [hdouble, hMopp] at huniq
    apply mem_iff_of_unique_factorization (H := H.toSubgroup)
      (Dynamic.centralizer_le_normalizer_unipotent χ X₀) huniq
    intro h hh
    obtain ⟨o, ho, z, hz, w, hw, hoH, hwH, e⟩ := hHfac h⁻¹ (H.inv_mem hh)
    have hzH : z ∈ H := by
      have : z = o⁻¹ * h⁻¹ * w⁻¹ := by rw [e]; group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.inv_mem hoH) (H.inv_mem hh)) (H.inv_mem hwH)
    refine ⟨w⁻¹, Subgroup.mem_inf.mpr ⟨H.inv_mem hwH, Subgroup.inv_mem _ hw⟩, z⁻¹,
      Subgroup.mem_inf.mpr ⟨H.inv_mem hzH, Subgroup.inv_mem _ hz⟩, o⁻¹,
      Subgroup.mem_inf.mpr ⟨H.inv_mem hoH, Subgroup.inv_mem _ ho⟩, ?_⟩
    calc h = (o * z * w)⁻¹ := by rw [← e, inv_inv]
      _ = _ := by group
  have hfac' : ∀ (m : (Dynamic.centralizer χ').carrier X₀) (u : unipotentPoints χ')
      (v : unipotentPoints (oppositeCocharacter χ')),
      (m : RationalPoint F G.X) * u * (v : RationalPoint F G.X) ∈ H ↔
        (m : RationalPoint F G.X) ∈ H ∧ (u : RationalPoint F G.X) ∈ H ∧
          (v : RationalPoint F G.X) ∈ H := by
    have huniq := RationalPointFamily.dynamic_opposite_factorization_unique
      (oppositeCocharacter χ')
    have hdouble : Dynamic.inverseCocharacter (oppositeCocharacter χ') = χ' :=
      Dynamic.inverseCocharacter_inverseCocharacter χ'
    have hMopp : Dynamic.centralizer (oppositeCocharacter χ') = Dynamic.centralizer χ' :=
      Dynamic.centralizer_inverseCocharacter χ'
    rw [hdouble, hMopp] at huniq
    apply mem_iff_of_unique_factorization (H := H.toSubgroup)
      (Dynamic.centralizer_le_normalizer_unipotent χ' X₀) huniq
    intro h hh
    obtain ⟨n, hn, b, hb, z, hz, c, hc, n', hn', e⟩ := hHfac' h hh
    set l := b * z * c
    have hlH : l⁻¹ ∈ H := H.inv_mem (hbzcH b hb z hz c hc)
    have hlL : l⁻¹ ∈ L := L.inv_mem (hbzcL b hb z hz c hc)
    obtain ⟨n₁, hn₁, b₁, hb₁, z₁, hz₁, c₁, hc₁, n₁', hn₁', e₁⟩ := hHfac' l⁻¹ hlH
    have h3 := hNLNu n₁ (Subgroup.mem_inf.mp hn₁).2 (b₁ * z₁ * c₁) (hbzcL b₁ hb₁ z₁ hz₁ c₁ hc₁)
      n₁' (Subgroup.mem_inf.mp hn₁').2 1 (one_mem _) l⁻¹ hlL 1 (one_mem _)
      (by rw [← e₁]; group)
    have hl : l = c₁⁻¹ * z₁⁻¹ * b₁⁻¹ := by
      rw [← inv_inv l, ← h3.2.1]; group
    have hc₁' : c₁⁻¹ ∈ unipotentPoints χ' := by
      have : c₁⁻¹ ∈ unipotentPoints (oppositeCocharacter χ) ⊓ L :=
        Subgroup.inv_mem _ (Subgroup.mem_inf.mp hc₁).2
      rw [hC] at this
      exact (Subgroup.mem_inf.mp this).1
    have hb₁' : b₁⁻¹ ∈ unipotentPoints (oppositeCocharacter χ') := by
      have : b₁⁻¹ ∈ unipotentPoints χ ⊓ L := Subgroup.inv_mem _ (Subgroup.mem_inf.mp hb₁).2
      rw [hB] at this
      exact (Subgroup.mem_inf.mp this).1
    refine ⟨n * c₁⁻¹, Subgroup.mem_inf.mpr ⟨H.mul_mem (Subgroup.mem_inf.mp hn).1
        (H.inv_mem (Subgroup.mem_inf.mp hc₁).1),
        Subgroup.mul_mem _ (hNU' (Subgroup.mem_inf.mp hn).2) hc₁'⟩,
      z₁⁻¹, Subgroup.mem_inf.mpr ⟨H.inv_mem (Subgroup.mem_inf.mp hz₁).1,
        hM ▸ Subgroup.inv_mem _ (Subgroup.mem_inf.mp hz₁).2⟩,
      b₁⁻¹ * n', Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem (Subgroup.mem_inf.mp hb₁).1)
        (Subgroup.mem_inf.mp hn').1,
        Subgroup.mul_mem _ hb₁' (hNV' (Subgroup.mem_inf.mp hn').2)⟩, ?_⟩
    rw [e, hl]
    group
  -- conclusion
  rw [gamma_eq_gammaIndex χ K hK hG hstable H hHK hfac,
    gamma_eq_gammaIndex χ' K hK hG hstable' H hHK hfac']
  unfold gammaIndex
  rw [hM]
  congr 2
  simp only [sourceTraceIndex_eq_relIndex]
  rw [← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← Nat.cast_mul, ← Nat.cast_mul, hidx]

end Langlands.Plancherel.RationalDynamicSource
