import Langlands.Representation.Induction.EmptyProductUnit
import Langlands.Representation.Filtration.CentralEigenspaceSplitting

/-! Irreducible rank-zero factors in the actual normalized binary product. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Classification

open CategoryTheory GeneralLinear CentralEigenspaceSplitting

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every irreducible smooth representation of the actual `GL_0` is isomorphic
to the actual binary product unit in its original carrier universe. -/
def rankZeroIrreducibleUnitIso
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier))
    (hA : letI := T.topology; Representation.IsIrreducible A.representation) :
    letI := T.topology
    A ≅ T.binaryProductUnit.{uF, uV} := by
  let := T.topology
  let := hA
  let v : A := Classical.choose (exists_ne_zero_of_isIrreducible hA)
  have hv : v ≠ 0 := Classical.choose_spec (exists_ne_zero_of_isIrreducible hA)
  let f : (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) ℂ).IntertwiningMap
      A.representation :=
    { toLinearMap := LinearMap.toSpanSingleton ℂ A v
      isIntertwining' := by
        intro g
        rw [GeneralLinear.representation_apply_of_rank_eq_zero rfl A.representation g]
        rfl }
  have hfn : f ≠ 0 := by
    intro h
    apply hv
    have h' := congrArg (fun q => q 1) h
    simpa [f] using h'
  have hfs : Function.Surjective f :=
    (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hfn
  have hfi : Function.Injective f := smul_left_injective ℂ hv
  let e := f.ofBijective ⟨hfi, hfs⟩
  let eU : (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) ℂ).Equiv
      (T.binaryProductUnit.{uF, uV}).representation :=
    Representation.Equiv.mk (ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm
      (fun _ => rfl)
  exact SmoothRep.mkIso (e.symm.trans eU)

private theorem irreducible_of_iso {G : Type uF} [Group G] [TopologicalSpace G]
    {A B : SmoothRep.{0, uF, max uF uV} ℂ G}
    (e : A ≅ B) (hB : Representation.IsIrreducible B.representation) :
    Representation.IsIrreducible A.representation :=
  (isIrreducible_iff_of_equiv (SmoothRep.equivOfIso e)).mpr hB

private theorem irreducible_comp_rank {a b : ℕ} (h : a = b)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear b F.Carrier) V)
    (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible
      (ρ.comp (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).toMonoidHom) := by
  subst b
  rw [GeneralLinear.reindex_finCongr_rfl]
  exact hρ

/-- A binary product with an irreducible rank-zero first factor is irreducible
whenever its second factor is irreducible, including rank zero. -/
theorem bernstein_binary_leftZero_irreducible (b : ℕ)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hA : letI := T.topology; Representation.IsIrreducible A.representation)
    (hB : letI := T.topology; Representation.IsIrreducible B.representation) :
    letI := T.topology
    Representation.IsIrreducible
      ((T.binaryNormalizedProductFunctor 0 b).obj (A, B)).representation := by
  let := T.topology
  have hcast := irreducible_comp_rank F (Nat.zero_add b) B.representation hB
  have hunit : Representation.IsIrreducible
      ((T.binaryNormalizedProductFunctor 0 b).obj (T.binaryProductUnit, B)).representation := by
    apply (isIrreducible_iff_of_equiv (T.binaryProductLeftUnitEquiv B)).mpr
    exact (isIrreducible_iff_of_equiv (BinaryTensor.liftEquiv _)).mp hcast
  exact irreducible_of_iso
    ((T.binaryNormalizedProductFunctor 0 b).mapIso
      ((rankZeroIrreducibleUnitIso F T A hA).prod (Iso.refl B))) hunit

/-- A binary product with an irreducible rank-zero second factor is irreducible
whenever its first factor is irreducible, including rank zero. -/
theorem bernstein_binary_rightZero_irreducible (a : ℕ)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
    (hA : letI := T.topology; Representation.IsIrreducible A.representation)
    (hB : letI := T.topology; Representation.IsIrreducible B.representation) :
    letI := T.topology
    Representation.IsIrreducible
      ((T.binaryNormalizedProductFunctor a 0).obj (A, B)).representation := by
  let := T.topology
  have hcast := irreducible_comp_rank F (Nat.add_zero a) A.representation hA
  have hunit : Representation.IsIrreducible
      ((T.binaryNormalizedProductFunctor a 0).obj (A, T.binaryProductUnit)).representation := by
    apply (isIrreducible_iff_of_equiv (T.binaryProductRightUnitEquiv A)).mpr
    exact (isIrreducible_iff_of_equiv (BinaryTensor.liftEquiv _)).mp hcast
  exact irreducible_of_iso
    ((T.binaryNormalizedProductFunctor a 0).mapIso
      ((Iso.refl A).prod (rankZeroIrreducibleUnitIso F T B hB))) hunit

end Langlands.Classification
