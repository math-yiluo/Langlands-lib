import Langlands.Weil.Representation.Structure
import Langlands.Weil.Representation.ContinuityProof
import Langlands.Weil.ProfiniteIntegerLiftingProof
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

noncomputable section
namespace Langlands.Weil

universe u v

private theorem frobenius_dense : DenseRange frobenius :=
  ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of Degree)

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  (φ : Γ →ₜ* ProfiniteIntegers)

omit [IsTopologicalGroup Γ] in
private theorem section_of_lifting (hφ : Function.Surjective φ)
    (hlift : ∀ f : Degree →* Γ, ∃ s : ProfiniteIntegers →ₜ* Γ,
      s.toMonoidHom.comp frobenius.toMonoidHom = f) :
    ∃ (t : Degree →* Pullback φ) (s : ProfiniteIntegers →ₜ* Γ),
      (∀ n, degree φ (t n) = n) ∧
      (∀ n, s (frobenius n) = projection φ (t n)) ∧
      (∀ z, φ (s z) = z) := by
  obtain ⟨g, hg⟩ := hφ (frobenius (Multiplicative.ofAdd (1 : ℤ)))
  let w : Pullback φ := ⟨(g, Multiplicative.ofAdd (1 : ℤ)), hg⟩
  let t := zpowersHom (Pullback φ) w
  have ht (n : Degree) : degree φ (t n) = n := by
    change degree φ (w ^ n.toAdd) = n
    rw [map_zpow]
    change (Multiplicative.ofAdd (1 : ℤ)) ^ n.toAdd = n
    apply Multiplicative.ext
    change n.toAdd • (1 : ℤ) = n.toAdd
    simp
  obtain ⟨s, hs⟩ := hlift ((projection φ).toMonoidHom.comp t)
  have hs' (n : Degree) : s (frobenius n) = projection φ (t n) :=
    DFunLike.congr_fun hs n
  refine ⟨t, s, ht, hs', ?_⟩
  have heq : (fun z => φ (s z)) = id := by
    apply frobenius_dense.equalizer (φ.continuous.comp s.continuous) continuous_id
    funext n
    change φ (s (frobenius n)) = frobenius n
    rw [hs']
    exact (t n).property.trans (congrArg frobenius (ht n))
  exact congrFun heq

private theorem projection_dense_of_section
    (s : ProfiniteIntegers →ₜ* Γ) (hs : ∀ z, φ (s z) = z) :
    DenseRange (projection φ) := by
  let p : inertia φ × ProfiniteIntegers → Γ := fun x => x.1.val * s x.2
  have hp : Continuous p :=
    (continuous_subtype_val.comp continuous_fst).mul (s.continuous.comp continuous_snd)
  have hp_surj : Function.Surjective p := by
    intro g
    let i : inertia φ := ⟨g * (s (φ g))⁻¹, by
      change φ (g * (s (φ g))⁻¹) = 1
      simp [hs]⟩
    exact ⟨(i, φ g), by simp [p, i]⟩
  have hd := hp_surj.denseRange.comp (denseRange_id.prodMap frobenius_dense) hp
  apply hd.mono
  rintro _ ⟨⟨i, n⟩, rfl⟩
  refine ⟨⟨(i.val * s (frobenius n), n), ?_⟩, rfl⟩
  change φ (i.val * s (frobenius n)) = frobenius n
  simp [hs, show φ i.val = 1 from i.property]

private theorem finite_integer_lift {M : Type v} [Monoid M] [TopologicalSpace M]
    (f : Degree →* M) (hf : (Set.range f).Finite) :
    ∃ F : ProfiniteIntegers →ₜ* M, ∀ n, F (frobenius n) = f n := by
  let q := QuotientGroup.lift f.ker f le_rfl
  have hqinj : Function.Injective q :=
    (QuotientGroup.injective_lift_iff f.ker f le_rfl).mpr rfl
  have hqrange : Set.range q = Set.range f := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨QuotientGroup.mk n, rfl⟩
  have : Finite (Set.range q) := (hqrange.symm ▸ hf).to_subtype
  have : Finite (Degree ⧸ f.ker) :=
    Finite.of_injective (Set.rangeFactorization q) (fun a b h => hqinj (congrArg Subtype.val h))
  have : f.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let N : FiniteIndexNormalSubgroup Degree := FiniteIndexNormalSubgroup.ofSubgroup f.ker
  let π : ProfiniteIntegers →ₜ* Degree ⧸ f.ker :=
    ((ProfiniteGrp.limitCone (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of Degree))).π.app N).hom
  let F : ProfiniteIntegers →ₜ* M :=
    { toMonoidHom := q.comp π.toMonoidHom
      continuous_toFun := (continuous_of_discreteTopology (f := q)).comp π.continuous }
  exact ⟨F, fun _ => rfl⟩

private theorem extend_finite_hom {M : Type v} [Monoid M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] (hφ : Function.Surjective φ)
    (hlift : ∀ f : Degree →* Γ, ∃ s : ProfiniteIntegers →ₜ* Γ,
      s.toMonoidHom.comp frobenius.toMonoidHom = f)
    (ρ : Pullback φ →ₜ* M) (hρ : (Set.range ρ).Finite) :
    ∃! σ : Γ →ₜ* M, σ.comp (projection φ) = ρ := by
  obtain ⟨t, s, ht, hst, hs⟩ := section_of_lifting φ hφ hlift
  have hd := projection_dense_of_section φ s hs
  obtain ⟨ψ, hψ⟩ := finite_integer_lift (ρ.toMonoidHom.comp t)
    (hρ.subset (by rintro _ ⟨n, rfl⟩; exact ⟨t n, rfl⟩))
  let i : Γ → inertia φ := fun g => ⟨g * (s (φ g))⁻¹, by
    change φ (g * (s (φ g))⁻¹) = 1
    simp [hs]⟩
  have hi : Continuous i :=
    (continuous_id.mul ((s.continuous.comp φ.continuous).inv)).subtype_mk _
  let F : Γ → M := fun g => ρ (inertiaInclusion φ (i g)) * ψ (φ g)
  have hF : Continuous F :=
    (ρ.continuous.comp ((inertiaInclusion φ).continuous.comp hi)).mul
      (ψ.continuous.comp φ.continuous)
  have hrest (w : Pullback φ) : F (projection φ w) = ρ w := by
    have hw : φ (projection φ w) = frobenius (degree φ w) := w.property
    dsimp only [F]
    rw [hw, hψ]
    change ρ (inertiaInclusion φ (i (projection φ w))) * ρ (t (degree φ w)) = ρ w
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · change projection φ w * (s (φ (projection φ w)))⁻¹ *
          projection φ (t (degree φ w)) = projection φ w
      rw [hw, hst]
      simp
    · change 1 * degree φ (t (degree φ w)) = degree φ w
      rw [one_mul, ht]
  have hone : F 1 = 1 := by
    simpa only [map_one] using hrest 1
  have hmul : ∀ g h, F (g * h) = F g * F h := by
    have heq : (fun x : Γ × Γ => F (x.1 * x.2)) =
        (fun x : Γ × Γ => F x.1 * F x.2) := by
      apply (hd.prodMap hd).equalizer
        (hF.comp (continuous_fst.mul continuous_snd))
        ((hF.comp continuous_fst).mul (hF.comp continuous_snd))
      funext x
      change F (projection φ x.1 * projection φ x.2) =
        F (projection φ x.1) * F (projection φ x.2)
      rw [← map_mul, hrest, hrest, hrest, map_mul]
    exact fun g h => congrFun heq (g, h)
  let σ : Γ →ₜ* M :=
    { toFun := F
      map_one' := hone
      map_mul' := hmul
      continuous_toFun := hF }
  refine ⟨σ, ?_, ?_⟩
  · ext w
    exact hrest w
  · intro σ' hσ'
    ext g
    apply congrFun (hd.equalizer σ'.continuous σ.continuous ?_) g
    funext w
    exact (DFunLike.congr_fun hσ' w).trans (hrest w).symm

private def continuousRepresentation
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hc : Continuous (fun g => (ρ g).toContinuousLinearMap)) : G →ₜ* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp
  continuous_toFun := hc

private theorem extend_finite_representation (hφ : Function.Surjective φ)
    (hlift : ∀ f : Degree →* Γ, ∃ s : ProfiniteIntegers →ₜ* Γ,
      s.toMonoidHom.comp frobenius.toMonoidHom = f)
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Pullback φ) V)
    (hc : Continuous (fun w => (ρ w).toContinuousLinearMap))
    (hf : (Set.range ρ).Finite) :
    ∃! σ : Representation ℂ Γ V,
      Continuous (fun g => (σ g).toContinuousLinearMap) ∧
      σ.comp (projection φ).toMonoidHom = ρ := by
  let ρc := continuousRepresentation ρ hc
  have hfc : (Set.range ρc).Finite := by
    change (Set.range (fun w => (ρ w).toContinuousLinearMap)).Finite
    rw [Set.range_comp']
    exact
      hf.image (fun f : V →ₗ[ℂ] V => f.toContinuousLinearMap)
  obtain ⟨σc, hσc, huniq⟩ := extend_finite_hom φ hφ hlift ρc hfc
  let σ : Representation ℂ Γ V :=
    { toFun g := (σc g).toLinearMap
      map_one' := by ext x; simp
      map_mul' g h := by ext x; simp }
  have hcont : Continuous (fun g => (σ g).toContinuousLinearMap) := σc.continuous
  have hrest : σ.comp (projection φ).toMonoidHom = ρ := by
    ext w x
    exact congrArg (fun f : V →L[ℂ] V => f x) (DFunLike.congr_fun hσc w)
  refine ⟨σ, ⟨hcont, hrest⟩, ?_⟩
  rintro σ' ⟨hc', hrest'⟩
  have heq : continuousRepresentation σ' hc' = σc := by
    apply huniq
    ext w x
    exact congrArg (fun f : V →ₗ[ℂ] V => f x) (DFunLike.congr_fun hrest' w)
  ext g x
  exact congrArg (fun f : V →L[ℂ] V => f x) (DFunLike.congr_fun heq g)

private theorem finiteImageExtension_of_lifting
    (hlift : ProfiniteIntegerLifting.{u}) :
    FiniteImageExtension.{u, v} := by
  intro G _ _ _ _ _ φ hφ V _ _ _ ρ hc
  constructor
  · intro hf
    exact extend_finite_representation φ hφ (fun f => (hlift G f).exists) ρ hc hf
  · rintro ⟨σ, ⟨hσc, hσρ⟩, _⟩
    have hf := continuous_compact_nonarchimedean_representation_finite_range G V σ hσc
    apply hf.subset
    rintro _ ⟨w, rfl⟩
    exact ⟨projection φ w, DFunLike.congr_fun hσρ w⟩

/-- Finite-image continuous representations of the integer pullback are precisely
those extending uniquely to the compact Hausdorff nonarchimedean ambient group. -/
theorem finiteImageExtension : FiniteImageExtension.{u, v} :=
  finiteImageExtension_of_lifting profiniteIntegerLifting

end Langlands.Weil
