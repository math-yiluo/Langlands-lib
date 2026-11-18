import Langlands.Representation.Jacquet.StandardCasselmanUniformAsymptotics
import Langlands.Representation.Jacquet.CompressionSeparationBound

/-! # Casselman asymptotics with depth bounded by a fixed-vector dimension -/

noncomputable section

universe u uV

namespace Langlands.Jacquet.StablePairingData

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {D : StablePairingData G}
  {ρ : Representation ℂ G V} {hρ : IsSmooth ρ}
  {b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ] Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ}

/-- A factor of the compression raised to a fixed-vector dimension bound puts
all fixed vectors in the stable image, so the pairing gives their exact coefficients. -/
theorem IsStablePairing.asymptotics_of_compressedAction_eq_pow_mul
    (hA : D.Admits ρ hρ) (hb : D.IsStablePairing ρ hρ b)
    (K : OpenSubgroup G) (hK : D.Good K)
    [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)]
    {d : ℕ} (hd : Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ d)
    {a : G} (ha : ∀ x ∈ K, x ∈ D.N → a⁻¹ * x * a ∈ K)
    (T : Module.End ℂ (fixedVectors ρ K.toSubgroup))
    (hprod : compressedAction ρ hρ K (D.isCompact K hK) a =
      compressedAction ρ hρ K (D.isCompact K hK) D.g⁻¹ ^ d * T)
    {v : V} (hv : v ∈ fixedVectors ρ K.toSubgroup)
    {ℓ : SmoothDual ρ} (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup) :
    smoothDualPairing ρ ℓ (ρ a v) =
      b (Jacquet.mk (smoothContragredient ρ) D.N ℓ) (Jacquet.mk ρ D.Nbar (ρ a v)) := by
  let hKc := D.isCompact K hK
  let C := compressedAction ρ hρ K hKc D.g⁻¹
  have hsplit : CompactCompressionSplits ρ hρ K hKc D.g⁻¹ :=
    powerKernelSup_isCompl_stableImage ρ hρ K hKc D.g⁻¹ inferInstance
  have hkill : ∀ v ∈ powerKernelSup ρ hρ K hKc D.g⁻¹, (C ^ d) v = 0 :=
    fun w hw => pow_apply_eq_zero_of_finrank_le C d hd w hw
  have hstable := (stabilization_of_pow_kill ρ hρ K hKc D.g⁻¹ hsplit d hkill d le_rfl).1
  let t := compressedAction ρ hρ K hKc a ⟨v, hv⟩
  have ht : t ∈ stableImage ρ hρ K hKc D.g⁻¹ := by
    rw [hstable]
    refine ⟨T ⟨v, hv⟩, ?_⟩
    simp only [t, hprod, Module.End.mul_apply]
  have hu : ∀ x ∈ K, x ∈ D.N → ρ x (ρ a v) = ρ a v := by
    intro x hx hxN
    calc
      ρ x (ρ a v) = ρ a (ρ (a⁻¹ * x * a) v) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 1
        group
      _ = ρ a v := by rw [apply_eq_of_mem_fixedVectors ρ hv (ha x hx hxN)]
  rw [← smoothDualPairing_averageMap ρ hρ K hKc hℓ (ρ a v),
    ← hb.apply_mk_averageMap hA K hK hℓ hu]
  exact (hb K hK ⟨ℓ, hℓ⟩ t ht).symm

end Langlands.Jacquet.StablePairingData

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Jacquet

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup

variable (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
  {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
  {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
  {ζ : cocharacterLattice S} (hζ : IsStandardCocharacter i ν J ζ)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  {A A₀ : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
  {q₀ : A₀.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)
  (hmem : ∀ K ∈ B, StandardParabolicBasisMember i ν J q K)
  (hA₀ : IsCompatibleStandardSplitComponent i ν ∅ A₀ q₀)
  (hmem₀ : ∀ K ∈ B, StandardParabolicBasisMember i ν ∅ q₀ K)

/-- A geometric depth bound gives the Casselman identity at dominant uniformizer
points with simple-root pairings outside `J` at least `d * c`, for all admissible
representations whose fixed vectors at the given basis level have dimension at most `d`. -/
def IsStandardCasselmanDepthBound (c : ℕ) : Prop :=
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      {K : Subgroup (rationalPoints G)} (_hK : K ∈ B)
      (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ)
      {b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
        Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ},
      (standardCasselmanPairingData hG hi hν hζ hB hA hmem).IsStablePairing ρ hρ.1 b →
      ∀ {d : ℕ}, Module.finrank ℂ (fixedVectors ρ K) ≤ d →
        ∀ {v : V}, v ∈ fixedVectors ρ K →
        ∀ {ℓ : SmoothDual ρ}, ℓ ∈ fixedVectors (smoothContragredient ρ) K →
        ∀ y : cocharacterLattice S,
          (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α y) →
          (∀ α ∈ simpleRelativeRoots i ν, α ∉ J → (d : ℤ) * c ≤ latticePairing S α y) →
          smoothDualPairing ρ ℓ (ρ (Aubert.General.uniformizerPowers i (.ofAdd y)) v) =
            b (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
              (Jacquet.mk ρ (standardUnipotentPoints i ν J)
                (ρ (Aubert.General.uniformizerPowers i (.ofAdd y)) v))

include hJ hA₀ hmem₀ in
/-- A basis shared by the faces `J` and `∅` admits a geometric Casselman depth bound. -/
theorem exists_standardCasselman_boundedDepth :
    ∃ c, IsStandardCasselmanDepthBound.{u, uV} hG hi hν hζ hB hA hmem c := by
  classical
  let D := standardCasselmanPairingData hG hi hν hζ hB hA hmem
  let g := hA.strictElement i ν hi hζ
  have hgplus := (hA.strictElement_spec i ν hi hζ).2.2.1
  obtain ⟨z, hgz, hzJ, hz⟩ := hA.exists_eq_uniformizerPowers hJ hgplus
  have hg : g = Aubert.General.uniformizerPowers i (.ofAdd z) := hgz
  let Δ := (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).toFinset
  let c := Δ.sup fun α => (latticePairing S α z).natAbs
  refine ⟨c, ?_⟩
  intro V _ _ K hK ρ hρ b hb d hd v hv ℓ hℓ y hy hdeep
  let K' := basisOpenSubgroup hB hK
  have hgood : D.Good K' := good_of_mem hG hi hν hζ hB hA hmem hK
  have hAd : D.Admits ρ hρ.1 := standardCasselmanPairingData_admits hG hi hν hζ hB hA hmem ρ hρ
  let hKc := D.isCompact K' hgood
  let a := Aubert.General.uniformizerPowers i (.ofAdd y)
  let y₀ := y - d • z
  let a₀ := Aubert.General.uniformizerPowers i (.ofAdd y₀)
  have hy₀ : ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α y₀ := by
    intro α hα
    change 0 ≤ latticePairing S α (y - d • z)
    rw [map_sub, map_nsmul, nsmul_eq_mul]
    by_cases hαJ : α ∈ J
    · rw [hzJ α hαJ, mul_zero, sub_zero]
      exact hy α hα
    · have hle : (latticePairing S α z).natAbs ≤ c :=
        Finset.le_sup (f := fun α => (latticePairing S α z).natAbs) (by simpa [Δ] using hα)
      have hc : latticePairing S α z ≤ (c : ℤ) :=
        Int.le_natAbs.trans (by exact_mod_cast hle)
      exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_left hc (Int.natCast_nonneg d)).trans
        (hdeep α hα hαJ))
  have hgpow : g ^ d = Aubert.General.uniformizerPowers i (.ofAdd (d • z)) := by
    rw [hg, ← map_pow, ofAdd_nsmul]
  have ha : a = g ^ d * a₀ := by
    change Aubert.General.uniformizerPowers i (.ofAdd y) =
      g ^ d * Aubert.General.uniformizerPowers i (.ofAdd (y - d • z))
    rw [hgpow, ← map_mul, ← ofAdd_add]
    congr 2
    abel
  have hν₀ : IsStandardCocharacter i ν ∅ ν := isStandardCocharacter_empty_self i ν
  have hch : ∀ w : cocharacterLattice S,
      (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α w) →
      Aubert.General.uniformizerPowers i (.ofAdd w) ∈ standardComponentCA i q₀ ∧
      Aubert.General.uniformizerPowers i (.ofAdd w) ∈ standardComponentCAplus i ν ∅ q₀ :=
    fun w hw => uniformizerPowers_mem_standardComponentChambers hi ⟨ν, hν₀⟩ hA₀ w
      (fun _ h => False.elim h) hw
  obtain ⟨ha₀CA, ha₀plus⟩ := hch y₀ hy₀
  have hgpowplus : g ^ d ∈ standardComponentCAplus i ν ∅ q₀ := by
    rw [hgpow]
    exact (hch _ (fun α hα => by rw [map_nsmul]; exact nsmul_nonneg (hz α hα) _)).2
  obtain ⟨hfac₀, hcon₀⟩ := hmem₀ K hK
  have hfactor : ∀ k ∈ K',
      ∃ l ∈ K'.toSubgroup ⊓ standardOppositeUnipotentPoints i ν ∅,
      ∃ m ∈ K'.toSubgroup ⊓ standardLeviPoints i ν ∅,
      ∃ u ∈ K'.toSubgroup ⊓ standardUnipotentPoints i ν ∅, k = l * m * u := by
    intro k hk
    obtain ⟨⟨l, m, n⟩, heq⟩ := hfac₀.2 ⟨k, hk⟩
    exact ⟨l, l.property, m, m.property, n, n.property, (congrArg Subtype.val heq).symm⟩
  have hlow : ∀ x ∈ standardComponentCAplus i ν ∅ q₀,
      ∀ l ∈ K'.toSubgroup ⊓ standardOppositeUnipotentPoints i ν ∅, x⁻¹ * l * x ∈ K' := by
    intro x hx l hl
    have h := (hcon₀.2.1 x hx).2 ⟨l, hl, rfl⟩
    simp only [inv_inv, SetLike.mem_coe] at h
    exact h.1
  have hmid : ∀ m ∈ K'.toSubgroup ⊓ standardLeviPoints i ν ∅, a₀⁻¹ * m * a₀ ∈ K' := by
    intro m hm
    have hm' : m ∈ ambientConjugate a₀ ((K ⊓ standardLeviPoints i ν ∅ :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
      rw [hcon₀.1 a₀ ha₀CA]
      exact hm
    obtain ⟨x, hx, heq⟩ := hm'
    have h : a₀⁻¹ * m * a₀ = x := by rw [← heq]; group
    rw [h]
    exact hx.1
  have hcontr : ∀ u ∈ K', u ∈ D.N → a⁻¹ * u * a ∈ K' := fun u hu huN =>
    hlow a (hch y hy).2 u ⟨hu, standardOppositeUnipotentPoints_le_empty hG hi hν hζ huN⟩
  have hDg : D.g⁻¹ = g := inv_inv g
  have hpow : compressedAction ρ hρ.1 K' hKc (g ^ d) =
      compressedAction ρ hρ.1 K' hKc D.g⁻¹ ^ d := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [← hDg]
    exact (D.compressedAction_inv_pow_apply ρ hρ.1 K' hgood d w).symm
  have hprod : compressedAction ρ hρ.1 K' hKc a =
      compressedAction ρ hρ.1 K' hKc D.g⁻¹ ^ d * compressedAction ρ hρ.1 K' hKc a₀ := by
    rw [ha, compressedAction_mul_of_factor ρ hρ.1 K' hKc _ _ _ hfactor (g ^ d) a₀
      (fun u hu => ((hcon₀.2.1 (g ^ d) hgpowplus).1 ⟨u, hu, rfl⟩).1)
      (hlow a₀ ha₀plus) hmid, hpow]
  let := hρ.2 K'
  exact StablePairingData.IsStablePairing.asymptotics_of_compressedAction_eq_pow_mul
    hAd hb K' hgood hd hcontr _ hprod hv hℓ

end Langlands.BruhatTits.SpecialCompact
