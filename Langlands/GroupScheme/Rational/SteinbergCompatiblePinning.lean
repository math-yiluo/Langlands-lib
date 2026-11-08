import Langlands.GroupScheme.Rational.SteinbergCompatibleRootMaps
import Langlands.GroupScheme.Lie.WeightLineGaloisCoordinates
import Langlands.GroupScheme.Rational.NormalizedRootExistenceProof

/-! # Compatible choices of simple-root pinning vectors -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option autoImplicit false

private theorem equivariant_choice_of_stabilizer_fixed
    {Γ : Type u} [Group Γ] {I : Type v} [MulAction Γ I]
    {V : Type w} [MulAction Γ V] (P : I → V → Prop)
    (hP : ∀ (g : Γ) (i : I) (x : V), P i x → P (g • i) (g • x))
    (hfixed : ∀ i : I, ∃ x : V, P i x ∧
      ∀ g : Γ, g • i = i → g • x = x) :
    ∃ f : I → V, (∀ i, P i (f i)) ∧
      ∀ (g : Γ) (i : I), g • f i = f (g • i) := by
  classical
  let Q := MulAction.orbitRel.Quotient Γ I
  let q : I → Q := Quotient.mk''
  let b : Q → V := fun o => (hfixed o.out).choose
  have hb (o : Q) : P o.out (b o) ∧
      ∀ g : Γ, g • o.out = o.out → g • b o = b o :=
    (hfixed o.out).choose_spec
  have ht (i : I) : ∃ g : Γ, g • (q i).out = i := by
    have h : (q i).out ∈ MulAction.orbit Γ i :=
      Quotient.exact (Quotient.out_eq' (q i))
    exact MulAction.mem_orbit_symm.mp h
  let t : I → Γ := fun i => (ht i).choose
  have hti (i : I) : t i • (q i).out = i := (ht i).choose_spec
  refine ⟨fun i => t i • b (q i), ?_, ?_⟩
  · intro i
    simpa only [hti] using hP (t i) (q i).out (b (q i)) (hb (q i)).1
  · intro g i
    have hq : q (g • i) = q i := MulAction.orbitRel.Quotient.quotient_smul_eq
    have hs : ((t (g • i))⁻¹ * g * t i) • (q i).out = (q i).out := by
      rw [mul_smul, mul_smul, hti]
      have hh := hti (g • i)
      rw [hq] at hh
      exact inv_smul_eq_iff.mpr hh.symm
    have hx := (hb (q i)).2 ((t (g • i))⁻¹ * g * t i) hs
    have he := congrArg (fun z : V => t (g • i) • z) hx
    simpa only [hq, mul_smul, smul_inv_smul] using he

private def lineCoordinate {L : Type u} [Field L] {V : Type v}
    [AddCommGroup V] [Module L V] (e : L ≃ₗ[L] V) (v : V) (hv : v ≠ 0) :
    L ≃ₗ[L] V := by
  have hd : Module.finrank L V = 1 := by simpa using e.finrank_eq.symm
  let l : L →ₗ[L] V := (LinearMap.id : L →ₗ[L] L).smulRight v
  exact LinearEquiv.ofBijective l
    ⟨fun _ _ h => smul_left_injective L hv h,
      fun y => exists_smul_eq_of_finrank_eq_one hd hv y⟩

namespace SplitPinning

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local notation "b" => algebraBaseMap k K
local notation "G_K" => CategoryTheory.Functor.obj
  (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance steinbergCompatiblePinningIsAffineHom : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

variable (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (j : T.toGrp ⟶ G)
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map j)
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ a)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root a)))

include hT in
private theorem weightSpace_eq_descended (χ : characterLattice p.torus) :
    weightSpace p.inclusion χ =
      weightSpace ((GroupScheme.baseChange b).map j) (characterLattice.congr eT χ) := by
  have hid : Lie.targetMapLinear (𝟙 G_K) (CommRingCat.of K) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [lieKernelHomLinear_val, Grp.id_hom_hom, Category.comp_id]
    rfl
  have h := weightSpace_map_of_transport eT (Iso.refl G_K)
    (by simpa only [Iso.refl_hom, Category.comp_id] using hT) χ
  simpa only [Iso.refl_hom, hid, Submodule.map_id] using h

include hT hroot in
private theorem galois_mem_simpleWeightSpace (σ : K ≃ₐ[k] K) (a : p.base.support)
    {x : Additive (lieKernel G_K (CommRingCat.of K))}
    (hx : x ∈ weightSpace p.inclusion (p.rootDatum.root a)) :
    Lie.baseChangeGaloisEquiv k K G σ x ∈
      weightSpace p.inclusion (p.rootDatum.root (ρ σ a)) := by
  rw [weightSpace_eq_descended k K p j eT hT] at hx ⊢
  have hx' : x ∈ RelativeRoot.actionWeightSpace
      ((AutomorphicAction.conjugation j).baseChange b)
      (characterLattice.congr eT (p.rootDatum.root a)) := by
    rw [AutomorphicAction.baseChange_conjugation, RelativeRoot.actionWeightSpace_conjugation]
    exact hx
  have h := RelativeRoot.galois_mem_actionWeightSpace k K
    (AutomorphicAction.conjugation j) σ _ hx'
  rw [AutomorphicAction.baseChange_conjugation, RelativeRoot.actionWeightSpace_conjugation,
    ← hroot σ a] at h
  exact h

include hT hroot in
private theorem exists_stabilizer_fixed_simpleVector [FiniteDimensional k K]
    (a : p.base.support) :
    ∃ x : Additive (lieKernel G_K (CommRingCat.of K)),
      (x ∈ weightSpace p.inclusion (p.rootDatum.root a) ∧ x ≠ 0) ∧
        ∀ σ : K ≃ₐ[k] K, ρ σ a = a → Lie.baseChangeGaloisEquiv k K G σ x = x := by
  let : MulAction (K ≃ₐ[k] K) p.base.support := MulAction.compHom _ ρ
  let H := MulAction.stabilizer (K ≃ₐ[k] K) a
  let χ := characterLattice.congr eT (p.rootDatum.root a)
  have hH (σ : H) : characterLattice.galoisRepresentation k K T σ.val χ = χ := by
    have hσ : ρ σ.val a = a := MulAction.mem_stabilizer_iff.mp σ.property
    exact (hroot σ.val a).symm.trans (congrArg
      (fun c : p.base.support => characterLattice.congr eT (p.rootDatum.root c)) hσ)
  have hd : Module.finrank K (weightSpace p.inclusion (p.rootDatum.root a)) = 1 := by
    have he := (p.pinning.trivialization a).finrank_eq
    simpa using he.symm
  have hV : Module.finrank K (RelativeRoot.actionWeightSpace
      ((AutomorphicAction.conjugation j).baseChange b) χ) = 1 := by
    rw [AutomorphicAction.baseChange_conjugation, RelativeRoot.actionWeightSpace_conjugation]
    change Module.finrank K (weightSpace ((GroupScheme.baseChange b).map j)
      (characterLattice.congr eT (p.rootDatum.root a))) = 1
    rw [← weightSpace_eq_descended k K p j eT hT]
    exact hd
  obtain ⟨e, he⟩ := RelativeRoot.exists_fixedWeight_equivariant_coordinates k K
    (AutomorphicAction.conjugation j) χ H hH hV
  refine ⟨(e 1).val, ⟨?_, ?_⟩, ?_⟩
  · rw [weightSpace_eq_descended k K p j eT hT]
    simpa only [AutomorphicAction.baseChange_conjugation,
      RelativeRoot.actionWeightSpace_conjugation] using (e 1).property
  · intro hz
    exact one_ne_zero (e.map_eq_zero_iff.mp (Subtype.ext hz))
  · intro σ hσ
    have hσH : σ ∈ H := MulAction.mem_stabilizer_iff.mpr hσ
    exact (he ⟨σ, hσH⟩ (1 : K)).trans
      (congrArg (fun z : K => (e z).val) σ.map_one)

include hT hroot in
private theorem exists_galoisCompatible_simpleVectors [FiniteDimensional k K] :
    ∃ f : p.base.support → Additive (lieKernel G_K (CommRingCat.of K)),
      (∀ a : p.base.support, f a ∈ weightSpace p.inclusion (p.rootDatum.root a) ∧ f a ≠ 0) ∧
        ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
          Lie.baseChangeGaloisEquiv k K G σ (f a) = f (ρ σ a) := by
  let : MulAction (K ≃ₐ[k] K) p.base.support := MulAction.compHom _ ρ
  let : DistribMulAction (K ≃ₐ[k] K)
      (Additive (lieKernel G_K (CommRingCat.of K))) :=
    Lie.baseChangeGaloisAction k K G
  let P (a : p.base.support) (x : Additive (lieKernel G_K (CommRingCat.of K))) :=
    x ∈ weightSpace p.inclusion (p.rootDatum.root a) ∧ x ≠ 0
  have hP (σ : K ≃ₐ[k] K) (a : p.base.support)
      (x : Additive (lieKernel G_K (CommRingCat.of K))) (hx : P a x) :
      P (σ • a) (σ • x) := by
    refine ⟨galois_mem_simpleWeightSpace k K p j eT hT ρ hroot σ a hx.1, ?_⟩
    intro hz
    exact hx.2 ((Lie.baseChangeGaloisEquiv k K G σ).map_eq_zero_iff.mp hz)
  have hfixed (a : p.base.support) :
      ∃ x : Additive (lieKernel G_K (CommRingCat.of K)), P a x ∧
        ∀ σ : K ≃ₐ[k] K, σ • a = a → σ • x = x :=
    exists_stabilizer_fixed_simpleVector k K p j eT hT ρ hroot a
  obtain ⟨f, hf, he⟩ := equivariant_choice_of_stabilizer_fixed P hP hfixed
  exact ⟨f, hf, he⟩

private def rootPinningOfVectors
    (f : p.base.support → Additive (lieKernel G_K (CommRingCat.of K)))
    (hf : ∀ a : p.base.support, f a ∈ weightSpace p.inclusion (p.rootDatum.root a) ∧ f a ≠ 0) :
    RootPinning p.inclusion p.rootDatum p.base where
  trivialization a := lineCoordinate (p.pinning.trivialization a) ⟨f a, (hf a).1⟩
    (fun h => (hf a).2 (congrArg Subtype.val h))

private theorem rootPinningOfVectors_rootVector
    (f : p.base.support → Additive (lieKernel G_K (CommRingCat.of K)))
    (hf : ∀ a : p.base.support, f a ∈ weightSpace p.inclusion (p.rootDatum.root a) ∧ f a ≠ 0)
    (a : p.base.support) :
    (rootPinningOfVectors k K p f hf).rootVector a = f a := by
  change (1 : K) • f a = f a
  exact one_smul K (f a)

include hT hroot in
private theorem exists_galoisCompatible_rootPinning [FiniteDimensional k K] :
    ∃ q : RootPinning p.inclusion p.rootDatum p.base,
      ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
        Lie.baseChangeGaloisEquiv k K G σ (q.rootVector a) = q.rootVector (ρ σ a) := by
  obtain ⟨f, hf, he⟩ := exists_galoisCompatible_simpleVectors k K p j eT hT ρ hroot
  refine ⟨rootPinningOfVectors k K p f hf, fun σ a => ?_⟩
  simpa only [rootPinningOfVectors_rootVector] using he σ a

/-- Choose actual simple-root trivializations whose root vectors are compatible
with every coefficient automorphism. -/
def galoisCompatibleRootPinning [FiniteDimensional k K] :
    RootPinning p.inclusion p.rootDatum p.base :=
  (exists_galoisCompatible_rootPinning k K p j eT hT ρ hroot).choose

/-- The chosen root vectors intertwine the supplied simple-root action with
canonical semilinear Lie transport. -/
theorem galoisCompatibleRootPinning_galois [FiniteDimensional k K]
    (σ : K ≃ₐ[k] K) (a : p.base.support) :
    Lie.baseChangeGaloisEquiv k K G σ
        ((galoisCompatibleRootPinning k K p j eT hT ρ hroot).rootVector a) =
      (galoisCompatibleRootPinning k K p j eT hT ρ hroot).rootVector (ρ σ a) :=
  (exists_galoisCompatible_rootPinning k K p j eT hT ρ hroot).choose_spec σ a

/-- Repin the supplied split group using the compatible actual root lines.
The torus, inclusion, root datum and base are those of the original pinning. -/
def galoisCompatibleRepinning [FiniteDimensional k K] : SplitPinning G_K :=
  { p with pinning := galoisCompatibleRootPinning k K p j eT hT ρ hroot }

/-- The constructed repinning has compatible vectors without supplying a
compatible vector family as a premise. -/
theorem galoisCompatibleRepinning_rootVectors [FiniteDimensional k K] :
    RootVectorsGaloisCompatible k K
      (galoisCompatibleRepinning k K p j eT hT ρ hroot) ρ :=
  galoisCompatibleRootPinning_galois k K p j eT hT ρ hroot

/-- Choose normalized whole root maps for the constructed compatible repinning. -/
def galoisCompatibleRootParametrizations [FiniteDimensional k K] :
    (galoisCompatibleRepinning k K p j eT hT ρ hroot).NormalizedSimpleRootParametrizations :=
  fun a => Classical.choice
    ((galoisCompatibleRepinning k K p j eT hT ρ hroot).nonempty_normalizedRootParametrization a)

/-- The constructed normalized root family is compatible as entire polynomial
root maps, with the variable fixed and the coefficients conjugated. -/
theorem galoisCompatibleRootParametrizations_compatible [FiniteDimensional k K] :
    RootMapsGaloisCompatible k K (galoisCompatibleRepinning k K p j eT hT ρ hroot)
      (galoisCompatibleRootParametrizations k K p j eT hT ρ hroot) ρ :=
  rootMapsGaloisCompatible_of_rootVectors k K
    (galoisCompatibleRepinning k K p j eT hT ρ hroot) j eT hT ρ hroot
    (galoisCompatibleRepinning_rootVectors k K p j eT hT ρ hroot)
    (galoisCompatibleRootParametrizations k K p j eT hT ρ hroot)

end SplitPinning
end Langlands.GroupScheme
