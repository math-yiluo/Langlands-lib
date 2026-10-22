import Langlands.Weil.Representation.Structure
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Algebra.Polynomial.Smeval
import Langlands.Weil.Local.DegreeCharacters
import Langlands.Weil.Representation.OperationClosureProof
import Langlands.Weil.Representation.UnramifiedDeterminant
import Langlands.Weil.Representation.ContinuityProof
import Langlands.LinearAlgebra.ComplexPolynomialRootsProof

noncomputable section

namespace Langlands.Weil

universe uW uG uV

section GroupAlgebra

variable {W : Type uW} [Group W] {G : Type uG} [Group G]

private theorem degree_zpow_lift (d : W →* Degree) {F : W}
    (hF : d F = Multiplicative.ofAdd (1 : ℤ)) (n : ℤ) :
    d (F ^ n) = Multiplicative.ofAdd n := by
  simp [map_zpow, hF, ← ofAdd_zsmul]

private theorem degree_decomposition (d : W →* Degree) {F : W}
    (hF : d F = Multiplicative.ofAdd (1 : ℤ)) (w : W) :
    ∃ i : d.ker, w = (i : W) * F ^ (d w).toAdd := by
  have hi : w * (F ^ (d w).toAdd)⁻¹ ∈ d.ker := by
    simp [MonoidHom.mem_ker, degree_zpow_lift d hF]
  exact ⟨⟨_, hi⟩, by simp⟩

private theorem image_mem_normalizer (d : W →* Degree) (f : W →* G) (w : W) :
    f w ∈ Subgroup.normalizer (d.ker.map f : Set G) := by
  intro x
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨w * i * w⁻¹, ?_, ?_⟩
    · simpa [MonoidHom.mem_ker] using (inferInstance : d.ker.Normal).conj_mem i hi w
    · simp
  · rintro ⟨i, hi, heq⟩
    refine ⟨w⁻¹ * i * w, ?_, ?_⟩
    · simpa using (inferInstance : d.ker.Normal).conj_mem i hi w⁻¹
    · rw [map_mul, map_mul, map_inv, heq]
      group

private theorem central_power_of_finite_inertia (d : W →* Degree) (f : W →* G)
    {F : W} (hF : d F = Multiplicative.ofAdd (1 : ℤ))
    (hI : (Set.range fun i : d.ker => f (i : W)).Finite) :
    ∃ m : ℕ, 0 < m ∧ ∀ w : W, Commute (f F ^ m) (f w) := by
  let H := d.ker.map f
  have hH : (H : Set G).Finite := by
    convert hI using 1
    ext x
    simp [H, Set.mem_range, Subtype.exists]
  let : Finite H := hH.to_subtype
  let a : Subgroup.normalizer (H : Set G) := ⟨f F, image_mem_normalizer d f F⟩
  obtain ⟨m, hm, hp⟩ := (isOfFinOrder_of_finite (H.normalizerMonoidHom a)).exists_pow_eq_one
  have hker : a ^ m ∈ H.normalizerMonoidHom.ker := by
    simpa [MonoidHom.mem_ker, map_pow] using hp
  rw [H.normalizerMonoidHom_ker] at hker
  have hc : ∀ i : d.ker, Commute (f F ^ m) (f i) := by
    intro i
    have hi : f i ∈ H := ⟨i, i.property, rfl⟩
    exact (hker (f i) hi).symm
  refine ⟨m, hm, fun w => ?_⟩
  obtain ⟨i, hi⟩ := degree_decomposition d hF w
  rw [hi, map_mul, map_zpow]
  exact (hc i).mul_right ((Commute.refl (f F)).pow_left m |>.zpow_right _)

private theorem finite_image_of_finite_inertia (d : W →* Degree) (f : W →* G)
    {F : W} (hF : d F = Multiplicative.ofAdd (1 : ℤ))
    (hI : (Set.range fun i : d.ker => f (i : W)).Finite)
    (hFfin : IsOfFinOrder (f F)) : (Set.range f).Finite := by
  have : Finite (Subgroup.zpowers (f F)) := finite_zpowers.mpr hFfin
  have hZ : (Set.range fun n : ℤ => f F ^ n).Finite := by
    simpa [Subgroup.coe_zpowers] using
      (Set.toFinite (Subgroup.zpowers (f F) : Set G))
  refine (hI.mul hZ).subset ?_
  rintro x ⟨w, rfl⟩
  obtain ⟨i, hi⟩ := degree_decomposition d hF w
  exact ⟨f i, ⟨i, rfl⟩, f F ^ (d w).toAdd, ⟨_, rfl⟩, by simpa only [map_mul, map_zpow] using congrArg f hi.symm⟩

private def commutingProduct {M : Type*} [Monoid M] (f g : W →* M)
    (h : ∀ w w', Commute (f w) (g w')) : W →* M where
  toFun w := f w * g w
  map_one' := by simp
  map_mul' w w' := by
    simp only [map_mul]
    calc
      f w * f w' * (g w * g w') = f w * (f w' * g w) * g w' := by
        simp only [mul_assoc]
      _ = f w * (g w * f w') * g w' := by rw [(h w' w).eq]
      _ = f w * g w * (f w' * g w') := by simp only [mul_assoc]

private theorem corrected_finite_image (d : W →* Degree) (f : W →* G)
    {F : W} (hF : d F = Multiplicative.ofAdd (1 : ℤ))
    (hI : (Set.range fun i : d.ker => f (i : W)).Finite)
    (b : G) (hb : ∀ w, Commute (f w) b)
    {m : ℕ} (hm : 0 < m) (hroot : b ^ m = f F ^ m) :
    let t := (zpowersHom G b⁻¹).comp d
    let s := commutingProduct f t (fun w _w' => (hb w).inv_right.zpow_right _)
    (Set.range s).Finite := by
  dsimp only
  let t := (zpowersHom G b⁻¹).comp d
  let s := commutingProduct f t (fun w w' => (hb w).inv_right.zpow_right _)
  have ht (i : d.ker) : t i = 1 := by
    change b⁻¹ ^ (d i).toAdd = 1
    have hi : d (i : W) = 1 := i.property
    simp [hi]
  have hs (i : d.ker) : s i = f i := by
    change f i * t i = f i
    rw [ht, mul_one]
  have hsF : s F = f F * b⁻¹ := by
    change f F * b⁻¹ ^ (d F).toAdd = _
    simp [hF]
  apply finite_image_of_finite_inertia d s hF
  · simpa only [hs] using hI
  · apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨m, hm, ?_⟩
    rw [hsF, (hb F).inv_right.mul_pow, inv_pow, hroot, mul_inv_cancel]

end GroupAlgebra

section Topology

variable {W : Type uW} [Group W] [TopologicalSpace W] [IsTopologicalGroup W]

private theorem degreeContinuous (d : W →* Degree) (hd : IsOpen (d.ker : Set W)) :
    Continuous d := by
  apply continuous_of_continuousAt_one d
  apply ContinuousAt.congr_of_eventuallyEq (f := fun _ : W => (1 : Degree)) continuousAt_const
  filter_upwards [hd.mem_nhds (d.ker.one_mem)] with w hw
  exact hw

end Topology

section Representations

variable {W : Type uW} [Group W]
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
private theorem polynomial_root_unit (ρ : Representation ℂ W V)
    (F : W) {m : ℕ} (hm : 0 < m)
    (hc : ∀ w, Commute (ρ.asGroupHom F ^ m) (ρ.asGroupHom w))
    (p : Polynomial ℂ) (hp : (Polynomial.aeval (ρ F ^ m) p) ^ m = ρ F ^ m) :
    ∃ b : (Module.End ℂ V)ˣ,
      b ^ m = ρ.asGroupHom F ^ m ∧ ∀ w, Commute (ρ.asGroupHom w) b := by
  have hu : IsUnit (Polynomial.aeval (ρ F ^ m) p) := by
    apply (isUnit_pow_iff (Nat.ne_of_gt hm)).mp
    rw [hp]
    exact (ρ.asGroupHom F).isUnit.pow m
  obtain ⟨b, hb⟩ := hu
  refine ⟨b, ?_, fun w => ?_⟩
  · apply Units.val_injective
    simpa only [Units.val_pow_eq_pow_val, Representation.asGroupHom_apply, hb] using hp
  · apply Units.val_injective
    change ρ w * (b : Module.End ℂ V) = (b : Module.End ℂ V) * ρ w
    rw [hb, Polynomial.aeval_eq_smeval]
    apply (Polynomial.smeval_commute_left ℂ p ?_).symm.eq
    exact congrArg Units.val (hc w)

omit [FiniteDimensional ℂ V] in
private theorem central_root_of_finite_inertia (d : W →* Degree)
    (ρ : Representation ℂ W V) {F : W}
    (hF : d F = Multiplicative.ofAdd (1 : ℤ))
    (hI : (Set.range fun i : d.ker => ρ (i : W)).Finite)
    (hroots : ∀ (A : Module.End ℂ V), IsUnit A →
      ∀ n : ℕ, 0 < n → ∃ p : Polynomial ℂ, (Polynomial.aeval A p) ^ n = A) :
    ∃ (m : ℕ) (b : (Module.End ℂ V)ˣ),
      0 < m ∧ b ^ m = ρ.asGroupHom F ^ m ∧
      ∀ w, Commute (ρ.asGroupHom w) b := by
  have hI' : (Set.range fun i : d.ker => ρ.asGroupHom (i : W)).Finite := by
    apply Set.Finite.of_finite_image (f := Units.val) ?_ Units.val_injective.injOn
    simpa only [← Set.range_comp', Representation.asGroupHom_apply] using hI
  obtain ⟨m, hm, hc⟩ := central_power_of_finite_inertia d ρ.asGroupHom hF hI'
  obtain ⟨p, hp⟩ := hroots (ρ F ^ m) ((ρ.asGroupHom F).isUnit.pow m) m hm
  obtain ⟨b, hb, hbcomm⟩ := polynomial_root_unit ρ F hm hc p hp
  exact ⟨m, b, hm, hb, hbcomm⟩

private def degreeCorrection (d : W →* Degree) (b : (Module.End ℂ V)ˣ) :
    W →* (Module.End ℂ V)ˣ := (zpowersHom _ b⁻¹).comp d

private def correctedRepresentation (d : W →* Degree) (ρ : Representation ℂ W V)
    (b : (Module.End ℂ V)ˣ) (hb : ∀ w, Commute (ρ.asGroupHom w) b) :
    Representation ℂ W V :=
  (Units.coeHom _).comp
    (commutingProduct ρ.asGroupHom (degreeCorrection d b)
      (fun w _ => (hb w).inv_right.zpow_right _))

omit [FiniteDimensional ℂ V] in
private theorem correctedRepresentation_apply (d : W →* Degree)
    (ρ : Representation ℂ W V) (b : (Module.End ℂ V)ˣ)
    (hb : ∀ w, Commute (ρ.asGroupHom w) b) (w : W) :
    correctedRepresentation d ρ b hb w =
      ρ w * (degreeCorrection d b w : Module.End ℂ V) := rfl

variable [TopologicalSpace W] [IsTopologicalGroup W]

private theorem continuous_degreeCorrection (d : W →* Degree)
    (hd : IsOpen (d.ker : Set W)) (b : (Module.End ℂ V)ˣ) :
    Continuous (fun w => LinearMap.toContinuousLinearMap
      (degreeCorrection d b w : Module.End ℂ V)) := by
  exact (continuous_of_discreteTopology :
    Continuous (fun n : Degree =>
      LinearMap.toContinuousLinearMap
        ((zpowersHom (Module.End ℂ V)ˣ b⁻¹ n : (Module.End ℂ V)ˣ) :
          Module.End ℂ V))).comp (degreeContinuous d hd)

private theorem correctedRepresentation_continuous (d : W →* Degree)
    (hd : IsOpen (d.ker : Set W)) (ρ : Representation ℂ W V)
    (hρ : Continuous (fun w => (ρ w).toContinuousLinearMap))
    (b : (Module.End ℂ V)ˣ) (hb : ∀ w, Commute (ρ.asGroupHom w) b) :
    Continuous (fun w => (correctedRepresentation d ρ b hb w).toContinuousLinearMap) := by
  change Continuous (fun w =>
    (Module.End.toContinuousLinearMap V) (ρ w * (degreeCorrection d b w : Module.End ℂ V)))
  simp only [map_mul]
  exact hρ.mul (continuous_degreeCorrection d hd b)

omit [FiniteDimensional ℂ V] [TopologicalSpace W] [IsTopologicalGroup W] in
private theorem correctedRepresentation_finite (d : W →* Degree)
    (ρ : Representation ℂ W V) {F : W} (hF : d F = Multiplicative.ofAdd (1 : ℤ))
    (hI : (Set.range fun i : d.ker => ρ (i : W)).Finite)
    (b : (Module.End ℂ V)ˣ) (hb : ∀ w, Commute (ρ.asGroupHom w) b)
    {m : ℕ} (hm : 0 < m) (hroot : b ^ m = ρ.asGroupHom F ^ m) :
    (Set.range (correctedRepresentation d ρ b hb)).Finite := by
  have hI' : (Set.range fun i : d.ker => ρ.asGroupHom (i : W)).Finite := by
    apply Set.Finite.of_finite_image (f := Units.val) ?_ Units.val_injective.injOn
    simpa only [← Set.range_comp', Representation.asGroupHom_apply] using hI
  have hf := corrected_finite_image d ρ.asGroupHom hF hI' b hb hm hroot
  simpa only [← Set.range_comp', correctedRepresentation, degreeCorrection,
    MonoidHom.coe_comp, Units.coeHom_apply, Function.comp_def] using
    hf.image (Units.val : (Module.End ℂ V)ˣ → _)

private theorem general_reduction_of_root (d : W →* Degree)
    (hd : IsOpen (d.ker : Set W)) (ρ : Representation ℂ W V)
    (hρ : Continuous (fun w => (ρ w).toContinuousLinearMap))
    {F : W} (hF : d F = Multiplicative.ofAdd (1 : ℤ))
    (hI : (Set.range fun i : d.ker => ρ (i : W)).Finite)
    (b : (Module.End ℂ V)ˣ) (hb : ∀ w, Commute (ρ.asGroupHom w) b)
    {m : ℕ} (hm : 0 < m) (hroot : b ^ m = ρ.asGroupHom F ^ m) :
    ∃ τ σ : Representation ℂ W V,
      Continuous (fun w => (τ w).toContinuousLinearMap) ∧
      (∀ i : d.ker, τ (i : W) = 1) ∧
      (∀ w w', Commute (ρ w) (τ w')) ∧
      (∀ w, σ w = ρ w * τ w) ∧
      Continuous (fun w => (σ w).toContinuousLinearMap) ∧
      (Set.range σ).Finite := by
  let τ : Representation ℂ W V := (Units.coeHom _).comp (degreeCorrection d b)
  refine ⟨τ, correctedRepresentation d ρ b hb, continuous_degreeCorrection d hd b,
    ?_, ?_, fun w => rfl, correctedRepresentation_continuous d hd ρ hρ b hb,
    correctedRepresentation_finite d ρ hF hI b hb hm hroot⟩
  · intro i
    have hi : d (i : W) = 1 := i.property
    change ((b⁻¹ ^ (d i).toAdd : (Module.End ℂ V)ˣ) : Module.End ℂ V) = 1
    simp [hi]
  · intro w w'
    exact congrArg Units.val ((hb w).inv_right.zpow_right (d w').toAdd).eq

omit [FiniteDimensional ℂ V] [TopologicalSpace W] [IsTopologicalGroup W] in
private theorem correctedRepresentation_scalar_twist (d : W →* Degree)
    (ρ : Representation ℂ W V) (b : (Module.End ℂ V)ˣ)
    (hb : ∀ w, Commute (ρ.asGroupHom w) b)
    (z : ℂˣ) (hz : (b : Module.End ℂ V) = (z : ℂ) • 1) :
    ρ = Langlands.twist ((zpowersHom ℂˣ z).comp d)
      (correctedRepresentation d ρ b hb) := by
  let e : ℂˣ →* (Module.End ℂ V)ˣ :=
    Units.map (algebraMap ℂ (Module.End ℂ V)).toMonoidHom
  have hb' : b = e z := by
    apply Units.val_injective
    change (b : Module.End ℂ V) = algebraMap ℂ (Module.End ℂ V) (z : ℂ)
    rw [Algebra.algebraMap_eq_smul_one]
    exact hz
  have ht (w : W) : (degreeCorrection d b w : Module.End ℂ V) =
      (((z ^ (d w).toAdd)⁻¹ : ℂˣ) : ℂ) • 1 := by
    change ((b⁻¹ ^ (d w).toAdd : (Module.End ℂ V)ˣ) : Module.End ℂ V) = _
    rw [hb', ← map_inv, ← map_zpow, inv_zpow]
    exact Algebra.algebraMap_eq_smul_one _
  ext w v
  change ρ w v = (z ^ (d w).toAdd : ℂˣ) •
    (correctedRepresentation d ρ b hb w) v
  rw [correctedRepresentation_apply, ht]
  simp [Units.smul_def, smul_smul, zpow_ne_zero _ z.ne_zero]

private theorem irreducible_reduction_of_scalar_root (d : W →* Degree)
    (hd : IsOpen (d.ker : Set W)) (ρ : Representation ℂ W V)
    (hρ : Continuous (fun w => (ρ w).toContinuousLinearMap))
    (hirr : Representation.IsIrreducible ρ)
    {F : W} (hF : d F = Multiplicative.ofAdd (1 : ℤ))
    (hI : (Set.range fun i : d.ker => ρ (i : W)).Finite)
    (b : (Module.End ℂ V)ˣ) (hb : ∀ w, Commute (ρ.asGroupHom w) b)
    {m : ℕ} (hm : 0 < m) (hroot : b ^ m = ρ.asGroupHom F ^ m)
    (z : ℂˣ) (hz : (b : Module.End ℂ V) = (z : ℂ) • 1) :
    ∃ (χ : W →* ℂˣ) (σ : Representation ℂ W V),
      Continuous χ ∧ (∀ i : d.ker, χ (i : W) = 1) ∧
      Continuous (fun w => (σ w).toContinuousLinearMap) ∧
      (Set.range σ).Finite ∧ Representation.IsIrreducible σ ∧
      ρ = Langlands.twist χ σ := by
  let χ := (zpowersHom ℂˣ z).comp d
  have heq := correctedRepresentation_scalar_twist d ρ b hb z hz
  refine ⟨χ, correctedRepresentation d ρ b hb, ?_, ?_,
    correctedRepresentation_continuous d hd ρ hρ b hb,
    correctedRepresentation_finite d ρ hF hI b hb hm hroot, ?_, heq⟩
  · exact (continuous_of_discreteTopology : Continuous (zpowersHom ℂˣ z)).comp
      (degreeContinuous d hd)
  · intro i
    have hi : d (i : W) = 1 := i.property
    change z ^ (d i).toAdd = 1
    simp [hi]
  · apply (OperationClosure.irreducible_twist_iff χ _).mp
    rwa [← heq]

end Representations

/-- General commuting correction, irreducible scalar reduction, and the
finite-order determinant criterion for complex Weil representations. -/
theorem unramifiedReduction : UnramifiedReduction.{uW, uV} := by
  intro W _ _ _ d _ _ hsurj hd V _ _ _ ρ hρ
  obtain ⟨F, hF⟩ := hsurj (Multiplicative.ofAdd (1 : ℤ))
  have hI : (Set.range fun i : d.ker => ρ (i : W)).Finite :=
    continuous_compact_nonarchimedean_representation_finite_range d.ker V
      (ρ.comp d.ker.subtype) (hρ.comp continuous_subtype_val)
  obtain ⟨m, b, hm, hroot, hb⟩ :=
    central_root_of_finite_inertia d ρ hF hI (Langlands.complexPolynomialRoots V)
  refine ⟨general_reduction_of_root d hd ρ hρ hF hI b hb hm hroot, ?_⟩
  intro hirr
  obtain ⟨z, hz⟩ := UnramifiedReductionAux.scalar_of_commuting_unit ρ hirr b
    (fun w => congrArg Units.val (hb w).eq)
  have htwist := irreducible_reduction_of_scalar_root d hd ρ hρ hirr hF hI
    b hb hm hroot z hz
  refine ⟨htwist, UnramifiedReductionAux.finite_range_iff_determinant_order_of_scalar_twist
    ρ hirr ?_⟩
  obtain ⟨χ, σ, _, _, _, hσ, _, heq⟩ := htwist
  exact ⟨χ, σ, hσ, heq⟩

end Langlands.Weil
