import Langlands.Global.AdelicIntertwiningLeviQuotient
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.AdelicRestrictionSplitCentreFiniteVolumeProof
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Square integrability of the individual normalized Levi slices -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open GroupScheme Automorphic.GroupSchemeFunctions RestrictionSplitCentre

section Compact

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]
  {K : Subgroup (AdelicGroupPoints F G)} {φ : AdelicGroupPoints F G → ℂ}

local notation "Gₐ" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "K∞" => K.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G))

/-- An archimedean compact-finite adelic function fixed by an open finite level has a
finite-dimensional space of right translates under the full maximal compact. -/
theorem finiteDimensional_compactRightTranslateSpan_of_adelicSmooth
    (hmax : IsMaximalCompactSubgroup F G K)
    (hs : IsAdelicSmoothFunction F G φ) (hfin : IsInfiniteSubgroupFiniteFunction F G K∞ φ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun g : Gₐ => φ (g * k.val))) := by
  classical
  obtain ⟨L, hLo, hL⟩ := hs.2.2
  let Kf := K.comap (ofFinite F G).toMonoidHom
  let D := L.subgroupOf Kf
  let : CompactSpace Kf := isCompact_iff_compactSpace.mp hmax.isMaximalCompact_comap_ofFinite.1
  let : Finite (Kf ⧸ D) :=
    Subgroup.quotient_finite_of_isOpen D (Subgroup.subgroupOf_isOpen Kf L hLo)
  let W := Submodule.span ℂ (Set.range fun k : K∞ => fun g : Gₐ => φ (g * ofInfinite F G k.val))
  let : FiniteDimensional ℂ W := hfin
  let R (q : Kf ⧸ D) : (Gₐ → ℂ) →ₗ[ℂ] (Gₐ → ℂ) :=
    { toFun := fun f g => f (g * ofFinite F G (q.out : Kf).val)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let : ∀ q : Kf ⧸ D, FiniteDimensional ℂ (W.map (R q)) := fun q => Module.Finite.map W _
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ q : Kf ⧸ D, W.map (R q))
    (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  let a : K∞ := ⟨infinite F G k.val, ((hmax.mem_iff k.val).mp k.property).1⟩
  let b : Kf := ⟨finite F G k.val, ((hmax.mem_iff k.val).mp k.property).2⟩
  let q : Kf ⧸ D := QuotientGroup.mk b
  obtain ⟨d, hd⟩ := QuotientGroup.mk_out_eq_mul D b
  have hd' : (q.out : Kf).val = b.val * (d.val : Gf) := congrArg Subtype.val hd
  have hdL : (d.val : Gf) ∈ L := d.property
  have hk : ofFinite F G b.val * ofInfinite F G a.val = k.val := by
    simp only [a, b, ofFinite_eq_pair, ofInfinite_eq_pair, pair_mul, one_mul, mul_one, pair_projections]
  refine Submodule.mem_iSup_of_mem q ⟨fun g => φ (g * ofInfinite F G a.val),
    Submodule.subset_span ⟨a, rfl⟩, funext fun g => ?_⟩
  change φ ((g * ofFinite F G (q.out : Kf).val) * ofInfinite F G a.val) = φ (g * k.val)
  rw [hd', map_mul, ← mul_assoc g, mul_assoc (g * ofFinite F G b.val),
    (factors_commute F G a.val (d.val : Gf)).eq.symm,
    ← mul_assoc (g * ofFinite F G b.val), hL _ hdL, mul_assoc, hk]

end Compact

section Levi

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {K : Subgroup (AdelicGroupPoints F G)}
  {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P} {φ : AdelicGroupPoints F G → ℂ}

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Every normalized Levi slice of a square-integrable inducing form is in `L²` of the
canonical Levi quotient. The finite-dimensional compact orbit upgrades Fubini's
almost-everywhere assertion to every compact point. -/
theorem memLp_normalizedLeviValue_slice (hmax : IsMaximalCompactSubgroup F G K)
    (hM : IsConnectedReductive M)
    (hφ : IsSquareIntegrableInducedForm K hmax.1 rho hsmooth hcalc p iU l φ) (k : K) :
    MemLp (fun q : CanonicalQuotient F M => normalizedLeviValue p l φ q.out k.val)
      2 (canonicalMeasure F M) := by
  let Γ := canonicalRationalSubgroup F M
  let Q := CanonicalQuotient F M
  let μK := compactHaarProbability F G K hmax.1
  let μQ := canonicalMeasure F M
  let : BorelSpace Q := canonicalQuotient_borelSpace F M centralSplitTorusCharacter hM
  let : IsFiniteMeasure μQ := connectedReductiveQuotientFiniteVolume F M hM _ _
    (isSplitComponent_canonicalRestrictionComponent F M)
  let v (s : K) (q : Q) := normalizedLeviValue p l φ q.out s.val
  have hv : Continuous (fun z : K × Q => v z.1 z.2) := by
    refine LeftCosetSpace.continuous_out_of_invariant Γ
      (fun (s : K) m => normalizedLeviValue p l φ m s.val) ?_ ?_
    · let h (z : K × AdelicGroupPoints F M) :
          AdelicGroupPoints F M × AdelicGroupPoints F G := (z.2, z.1.val)
      have hh : Continuous h := continuous_snd.prodMk
        (continuous_subtype_val.comp continuous_fst)
      let f (z : AdelicGroupPoints F M × AdelicGroupPoints F G) :=
        normalizedLeviValue p l φ z.1 z.2
      have hf : Continuous f := continuous_normalizedLeviValue p l (φ := φ) hφ.1.2.1.1
      change Continuous (f ∘ h)
      exact hf.comp hh
    · exact fun s => normalizedLeviValue_invariant p l hφ.1.1 hφ.2.1 s.val
  have hint : Integrable (fun z : K × Q => ‖v z.1 z.2‖ ^ 2) (μK.prod μQ) := by
    simpa only [v, sq_norm_normalizedLeviValue] using hφ.2.2
  have hae : ∀ᵐ s ∂μK, MemLp (v s) 2 μQ := by
    filter_upwards [hint.prod_right_ae] with s hs
    have hc : Continuous (v s) := by
      change Continuous ((fun z : K × Q => v z.1 z.2) ∘ (fun q : Q => (s, q)))
      exact hv.comp (Continuous.prodMk_right s)
    exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr hs
  let T := Submodule.span ℂ (Set.range fun s : K => fun g : AdelicGroupPoints F G => φ (g * s.val))
  let : FiniteDimensional ℂ T :=
    finiteDimensional_compactRightTranslateSpan_of_adelicSmooth hmax hφ.1.2.1 hφ.1.2.2.1
  let L : (AdelicGroupPoints F G → ℂ) →ₗ[ℂ] (Q → ℂ) :=
    { toFun := fun f q => normalizedLeviValue p l f q.out 1
      map_add' := fun f g => by ext q; simp [normalizedLeviValue, mul_add]
      map_smul' := fun c f => by ext q; simp [normalizedLeviValue, mul_left_comm] }
  let W := T.map L
  let : FiniteDimensional ℂ W := Module.Finite.map T L
  have hvW (s : K) : v s ∈ W :=
    ⟨fun g => φ (g * s.val), Submodule.subset_span ⟨s, rfl⟩, by
      funext q
      simp [L, v, normalizedLeviValue]⟩
  let LpFunctions : Submodule ℂ (Q → ℂ) :=
    { carrier := {f | MemLp f 2 μQ}
      zero_mem' := MemLp.zero
      add_mem' := fun hf hg => hf.add hg
      smul_mem' := fun c _ hf => hf.const_smul c }
  let V := W ⊓ LpFunctions
  let : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le (inf_le_left : V ≤ W)
  have hvPi : Continuous v := by
    apply continuous_pi
    intro q
    change Continuous ((fun z : K × Q => v z.1 z.2) ∘ (fun s : K => (s, q)))
    exact hv.comp (Continuous.prodMk_left q)
  have hclosed : IsClosed {s | v s ∈ V} := V.closed_of_finiteDimensional.preimage hvPi
  have hfull : (∀ᵐ s ∂μK, v s ∈ V) := hae.mono fun s hs => ⟨hvW s, hs⟩
  have huniv := (μK.dense_of_ae hfull).closure_eq
  rw [hclosed.closure_eq] at huniv
  have hk : k ∈ {s | v s ∈ V} := by
    rw [huniv]
    exact Set.mem_univ k
  exact (show v k ∈ V from hk).2

end Levi

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions RestrictionSplitCentre

/-- For every point of the given maximal compact, the normalized Levi slice of a
square-integrable inducing form is square integrable on the canonical quotient. -/
def NormalizedLeviSliceL2Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
    [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom],
    ∀ (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P) (K : Subgroup (AdelicGroupPoints F G))
      (hmax : IsMaximalCompactSubgroup F G K) {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (φ : AdelicGroupPoints F G → ℂ),
      IsConnectedReductive M →
      IsSquareIntegrableInducedForm K hmax.1 rho hsmooth hcalc p iU l φ →
      ∀ k : K, MemLp (fun q : CanonicalQuotient F M => normalizedLeviValue p l φ q.out k.val)
        2 (canonicalMeasure F M)

theorem normalizedLeviSliceL2 : NormalizedLeviSliceL2Statement := by
  intro F _ _ G P M U _ _ _ _ _ _ p iU l K hmax N d rho hsmooth hcalc φ hM hφ k
  exact memLp_normalizedLeviValue_slice hmax hM hφ k

end Langlands.Global
