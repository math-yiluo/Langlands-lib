import Langlands.Representation.Smooth.Schur.Statement
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

omit [TopologicalSpace G] in
private theorem schur_nontrivial (rho : Representation ℂ G V) [rho.IsIrreducible] :
    Nontrivial V := by
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) rho.asModule

/-- Admissibility supplies enough finite dimension to make every irreducible
endomorphism scalar. -/
theorem admissibleSchur_scalarEndomorphism (rho : Representation ℂ G V)
    (ha : IsAdmissible rho) (hi : rho.IsIrreducible) (f : rho.IntertwiningMap rho) :
    ∃! c : ℂ, f = c • Representation.IntertwiningMap.id rho := by
  let := hi
  let := schur_nontrivial rho
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨K, hK⟩ := ha.1 v
  let S := fixedVectors rho K.toSubgroup
  have hpres : ∀ x ∈ S, f.toLinearMap x ∈ S := by
    intro x hx g
    change rho (g : G) (f x) = f x
    rw [← f.isIntertwining]
    exact congrArg f (hx g)
  let fS : Module.End ℂ S := f.toLinearMap.restrict hpres
  let : Module.Finite ℂ S := ha.2 K
  let : Nontrivial S := ⟨⟨⟨v, hK⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := fS.exists_eigenvalue
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hx0 : (x : V) ≠ 0 := fun h => hx.2 (Subtype.ext h)
  have heig : f (x : V) = c • (x : V) := congrArg Subtype.val hx.apply_eq_smul
  have hscalar : f = c • Representation.IntertwiningMap.id rho := by
    apply sub_eq_zero.mp
    apply (Representation.IsIrreducible.injective_or_eq_zero
      (f - c • Representation.IntertwiningMap.id rho)).resolve_left
    intro hinj
    apply hx0
    apply hinj
    simpa using sub_eq_zero.mpr heig
  refine ⟨c, hscalar, ?_⟩
  intro d hd
  have heq := congrArg (fun t : rho.IntertwiningMap rho => t v) (hd.symm.trans hscalar)
  exact (smul_left_injective ℂ hv) heq

/-- An isomorphism identifies the intertwiner space with the scalar field. -/
theorem admissibleSchur_homEquiv (rho : Representation ℂ G V)
    (ha : IsAdmissible rho) (hi : rho.IsIrreducible)
    (sigma : Representation ℂ G W) (e : rho.Equiv sigma) :
    Nonempty ((rho.IntertwiningMap sigma) ≃ₗ[ℂ] ℂ) := by
  let := hi
  let := schur_nontrivial rho
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let L : ℂ →ₗ[ℂ] rho.IntertwiningMap sigma :=
    LinearMap.toSpanSingleton ℂ _ e.toIntertwiningMap
  have hinj : Function.Injective L := by
    intro a b h
    have he : e v ≠ 0 := by
      intro he
      apply hv
      exact e.injective (by simpa using he)
    exact (smul_left_injective ℂ he) (congrArg (fun f => f v) h)
  have hsurj : Function.Surjective L := by
    intro f
    obtain ⟨c, hc, _⟩ := admissibleSchur_scalarEndomorphism rho ha hi
      (e.symm.toIntertwiningMap.comp f)
    refine ⟨c, ?_⟩
    ext x
    apply e.symm.injective
    have h := congrArg (fun t : rho.IntertwiningMap rho => t x) hc
    simpa [L, LinearMap.toSpanSingleton_apply] using h.symm
  exact ⟨(LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).symm⟩

/-- The center has a unique locally constant scalar character. -/
theorem admissibleSchur_centralCharacter [IsTopologicalGroup G]
    (rho : Representation ℂ G V) (ha : IsAdmissible rho) (hi : rho.IsIrreducible) :
    ∃! chi : Subgroup.center G →* ℂˣ,
      IsLocallyConstant (chi : Subgroup.center G → ℂˣ) ∧
      ∀ (z : Subgroup.center G) (v : V), rho (z : G) v = (chi z : ℂ) • v := by
  classical
  let := hi
  let := schur_nontrivial rho
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let T (z : Subgroup.center G) : rho.IntertwiningMap rho :=
    { toLinearMap := rho z
      isIntertwining' := fun g => by
        change rho (z : G) * rho g = rho g * rho (z : G)
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp z.property g)] }
  have hs (z : Subgroup.center G) := admissibleSchur_scalarEndomorphism rho ha hi (T z)
  choose c hc huniq using hs
  have act (z : Subgroup.center G) (x : V) : rho (z : G) x = c z • x :=
    congrArg (fun f : rho.IntertwiningMap rho => f x) (hc z)
  have c_one : c 1 = 1 := by
    apply smul_left_injective ℂ hv
    dsimp only
    rw [← act]
    simp
  have c_mul (z w : Subgroup.center G) : c (z * w) = c z * c w := by
    apply smul_left_injective ℂ hv
    dsimp only
    rw [← act]
    change rho ((z : G) * (w : G)) v = _
    rw [map_mul, Module.End.mul_apply, act, act, smul_smul]
  have c_ne (z : Subgroup.center G) : c z ≠ 0 := by
    intro hz
    have h := c_mul z⁻¹ z
    rw [inv_mul_cancel, c_one, hz, mul_zero] at h
    exact one_ne_zero h
  let chi : Subgroup.center G →* ℂˣ :=
    { toFun := fun z => Units.mk0 (c z) (c_ne z)
      map_one' := Units.ext c_one
      map_mul' := fun z w => Units.ext (c_mul z w) }
  have chi_act (z : Subgroup.center G) (x : V) :
      rho (z : G) x = (chi z : ℂ) • x := act z x
  have hlc : IsLocallyConstant (chi : Subgroup.center G → ℂˣ) := by
    obtain ⟨K, hK⟩ := ha.1 v
    apply (IsLocallyConstant.iff_exists_open _).2
    intro z
    refine ⟨{w | (z : G)⁻¹ * (w : G) ∈ K},
      K.isOpen.preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩
    · simp
    · intro w hw
      apply Units.ext
      apply smul_left_injective ℂ hv
      dsimp only
      rw [← chi_act, ← chi_act]
      calc
        rho (w : G) v = rho (z : G) (rho ((z : G)⁻¹ * (w : G)) v) := by
          rw [← Module.End.mul_apply, ← map_mul]
          simp
        _ = rho (z : G) v := congrArg (rho (z : G)) (hK ⟨_, hw⟩)
  refine ⟨chi, ⟨hlc, chi_act⟩, ?_⟩
  intro psi hpsi
  ext z
  apply smul_left_injective ℂ hv
  dsimp only
  rw [← hpsi.2, ← chi_act]

/-- The complete published admissible Schur statement, with its original telescope. -/
theorem admissibleSchur
    {G : Type uG} [Group G] [TopologicalSpace G]
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :
    AdmissibleSchurStatement (G := G) (V := V) (W := W) := by
  intro _ rho ha hi
  refine ⟨admissibleSchur_scalarEndomorphism rho ha hi, ?_,
    admissibleSchur_centralCharacter rho ha hi⟩
  intro sigma _ hsi
  constructor
  · rintro ⟨e⟩
    exact admissibleSchur_homEquiv rho ha hi sigma e
  · intro hn f
    let := hi
    let := hsi
    exact (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_left
      (fun hb => hn ⟨f.ofBijective hb⟩)

example : ∀ {G : Type uG} [Group G] [TopologicalSpace G]
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W],
    AdmissibleSchurStatement (G := G) (V := V) (W := W) := @admissibleSchur

end Langlands
