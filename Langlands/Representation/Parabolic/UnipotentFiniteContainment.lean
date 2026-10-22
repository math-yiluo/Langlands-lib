import Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Representation.Geometric.RefinementDefinitions
import Langlands.Representation.Conductor.Congruence
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity

noncomputable section

namespace Langlands.Parabolic

universe uF

private theorem block_conj_integral {F : Type uF} [Field F] [ValuativeRel F]
    {n : ℕ} (B : GeneralLinear.BlockShape n) (d : F) (hd : d ≠ 0)
    (hdi : d ∈ (ValuativeRel.valuation F).integer)
    (g : B.unipotentRadical F)
    (hg : ∀ i j, d * g.val.val i j ∈ (ValuativeRel.valuation F).integer) :
    ∀ i j, (B.blockScalar F (fun k => (Units.mk0 d hd) ^ (-(k.val : ℤ))) *
      g.val.val * (B.blockScalar F (fun k => (Units.mk0 d hd) ^ (-(k.val : ℤ))))⁻¹) i j ∈
      (ValuativeRel.valuation F).integer := by
  intro x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  change (_ * g.val.val * _) (B.index i a) (B.index j b) ∈ _
  rw [B.blockScalar_conj_apply]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Units.val_mk0, zpow_neg, zpow_natCast, inv_inv]
  rcases lt_trichotomy i j with hij | rfl | hji
  · have he : j.val = i.val + (j.val - i.val - 1) + 1 := by
      have := Fin.lt_def.mp hij
      omega
    have heq : ((d ^ i.val)⁻¹ * d ^ j.val) * g.val.val (B.index i a) (B.index j b) =
        d ^ (j.val - i.val - 1) * (d * g.val.val (B.index i a) (B.index j b)) := by
      conv_lhs => rw [he, pow_add, pow_add, pow_one]
      field_simp
    rw [heq]
    exact ((ValuativeRel.valuation F).integer).mul_mem
      (((ValuativeRel.valuation F).integer).pow_mem hdi _) (hg _ _)
  · rw [(B.mem_unipotentRadical_iff F g.val).mp g.property]
    split_ifs <;> simp [hd]
  · rw [(B.mem_parabolic_iff F g.val.val).mp g.val.property i j a b hji]
    simp

/-- Every finite subset of the actual block radical lies in a compact open subgroup. -/
theorem unipotentFiniteContainment {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) : UnipotentFiniteContainmentClause F T B := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro s
  cases n with
  | zero =>
      exact ⟨⊤, Set.finite_univ.isCompact, fun _ _ => trivial⟩
  | succ n =>
      let entries (g : B.unipotentRadical F.Carrier) : Finset F.Carrier :=
        (Finset.univ.image (fun ij : Fin (n + 1) × Fin (n + 1) => g.val.val ij.1 ij.2)) ∪
        (Finset.univ.image (fun ij : Fin (n + 1) × Fin (n + 1) => (g⁻¹).val.val ij.1 ij.2))
      obtain ⟨d, hd, hdi, hs⟩ := RankinSelberg.common_integer_denominator (s.biUnion entries)
      let D := B.blockScalar F.Carrier (fun k => (Units.mk0 d hd) ^ (-(k.val : ℤ)))
      let e := (Homeomorph.mulLeft D).trans (Homeomorph.mulRight D⁻¹)
      let inclusion := (B.parabolic F.Carrier).subtype.comp (B.unipotentRadical F.Carrier).subtype
      let f := (MulAut.conj D).toMonoidHom.comp inclusion
      have hf : Continuous f := e.continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val)
      let K := OpenSubgroup.comap f hf (Conductor.levelOpenSubgroup F.Carrier n 0)
      refine ⟨K, ?_, ?_⟩
      · exact (e.isClosedEmbedding.comp ((B.isClosed_parabolic F.Carrier).isClosedEmbedding_subtypeVal.comp
          (B.isClosed_unipotentRadical F.Carrier).isClosedEmbedding_subtypeVal)).isCompact_preimage
            (Conductor.isCompact_levelOpenSubgroup F.Carrier n 0)
      · intro g hg
        have hentries (x) (hx : x ∈ entries g) := hs x (Finset.mem_biUnion.mpr ⟨g, hg, hx⟩)
        change f g ∈ Conductor.levelSubgroup F.Carrier n 0
        rw [Conductor.levelSubgroup_zero, Conductor.mem_integralSubgroup]
        constructor
        · apply block_conj_integral B d hd hdi g
          intro i j
          exact hentries _ (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩))
        · have he : (f g)⁻¹ = D * (g⁻¹).val.val * D⁻¹ := by
            simp [f, inclusion, MulAut.conj_apply, mul_assoc]
          rw [he]
          apply block_conj_integral B d hd hdi g⁻¹
          intro i j
          exact hentries _ (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩))

end Langlands.Parabolic

namespace Langlands.GeneralLinear.BlockShape

universe u
variable {n : ℕ} (B : BlockShape n) (R : Type u) [CommRing R] [TopologicalSpace R]

/-- Forgetting the intermediate parabolic gives a continuous group equivalence
between the intrinsic radical and its actual ambient matrix subgroup. -/
def unipotentRadicalAmbientEquiv : B.unipotentRadical R ≃ₜ* B.unipotentSubgroup R where
  toFun u := ⟨u.val.val, ⟨u.val, u.property, rfl⟩⟩
  invFun g := ⟨⟨g.val, ((B.mem_unipotentSubgroup_iff R g.val).mp g.property).1⟩,
    (B.mem_unipotentRadical_iff R _).mpr
      ((B.mem_unipotentSubgroup_iff R g.val).mp g.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

end Langlands.GeneralLinear.BlockShape

namespace Langlands.Geometric

universe u
variable {n : ℕ} (B : GeneralLinear.BlockShape n) (S : BlockRefinement B)
    (R : Type u) [CommRing R] [TopologicalSpace R]

/-- The actual product-Levi radical is continuously isomorphic to the finite
product of intrinsic block radicals, using their existing subgroup topologies. -/
def refinedUnipotentRadicalEquiv :
    refinedUnipotent R B S ≃ₜ* (∀ i, (S i).unipotentRadical R) where
  toFun g i := ((S i).unipotentRadicalAmbientEquiv R).symm
    ⟨g.val i, (mem_refinedUnipotent R B S g.val).mp g.property i⟩
  invFun u := ⟨fun i => ((S i).unipotentRadicalAmbientEquiv R (u i)).val,
    (mem_refinedUnipotent R B S _).mpr fun i =>
      ((S i).unipotentRadicalAmbientEquiv R (u i)).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_pi fun i =>
    ((S i).unipotentRadicalAmbientEquiv R).symm.continuous.comp
      (((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (continuous_pi fun i =>
    continuous_subtype_val.comp
      (((S i).unipotentRadicalAmbientEquiv R).continuous.comp (continuous_apply i))).subtype_mk _

end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

universe uF
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Every finite subset of an actual product-Levi refinement radical lies in a
compact open subgroup, without a properness or positive-rank assumption. -/
theorem refinedUnipotent_finite_containment (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    ∀ s : Finset (Geometric.refinedUnipotent F.Carrier B S),
      ∃ K : OpenSubgroup (Geometric.refinedUnipotent F.Carrier B S),
        IsCompact (K : Set (Geometric.refinedUnipotent F.Carrier B S)) ∧
        ∀ u ∈ s, u ∈ K := by
  classical
  let := T.topology
  intro s
  let e := Geometric.refinedUnipotentRadicalEquiv B S F.Carrier
  have h (i : Fin B.length) :=
    Parabolic.unipotentFiniteContainment F T (S i) (s.image fun u => e u i)
  choose K hcompact hmem using h
  let L : OpenSubgroup (∀ i, (S i).unipotentRadical F.Carrier) :=
    { toSubgroup := Subgroup.pi Set.univ (fun i => (K i).toSubgroup)
      isOpen' := isOpen_set_pi Set.finite_univ (fun i _ => (K i).isOpen) }
  refine ⟨OpenSubgroup.comap e.toMonoidHom e.continuous L, ?_, ?_⟩
  · exact e.toHomeomorph.isClosedEmbedding.isCompact_preimage (isCompact_univ_pi hcompact)
  · intro u hu
    change ∀ i ∈ (Set.univ : Set (Fin B.length)), e u i ∈ K i
    intro i _
    exact hmem i _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)

end Langlands.PadicField.TopologicalData
