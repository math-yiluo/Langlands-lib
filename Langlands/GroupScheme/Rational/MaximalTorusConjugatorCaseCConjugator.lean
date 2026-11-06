import Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseCAssembly
import Langlands.GroupScheme.Lie.BaseChange
import Langlands.GroupScheme.SubgroupBaseChange

/-! # A centralizer conjugator from a conjugation of Lie elements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section Transport

variable {k E : Type u} [CommRing k] [CommRing E] [Algebra k E]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  {A : Type u} [CommRing A] [Algebra k A] [Algebra E A] [IsScalarTower k E A]

local notation "G_E" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k E)) G

/-- A point of the base change of `G` on an affine test belongs to the base change of a
subgroup functor exactly when the corresponding point of `G` on the same algebra belongs to
it. -/
theorem SubgroupFunctor.mem_baseChange_affine_iff (F : SubgroupFunctor G)
    (g : Lie.AffinePoints G_E A) :
    g ∈ (F.baseChange (algebraBaseMap k E)).carrier
        ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E A))) ↔
      Lie.affineBaseChangeEquiv k E G A g ∈
        F.carrier ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))) := by
  rw [SubgroupFunctor.mem_baseChange]
  constructor
  · intro h
    exact F.comp_mem (Lie.affineBaseTestIso k E A).inv h
  · intro h
    have h' := F.comp_mem (Lie.affineBaseTestIso k E A).hom h
    change (Lie.affineBaseTestIso k E A).hom ≫ (Lie.affineBaseTestIso k E A).inv ≫ _ ∈ _ at h'
    rwa [Iso.hom_inv_id_assoc] at h'

variable [IsAffineHom G.X.hom]

local instance caseCConjugatorIsAffineHom : IsAffineHom (G_E).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

/-- Membership in the centralizer of a Lie element of the base change, on an affine test, is
the adjoint equation for the corresponding point and Lie element of `G`. -/
theorem Lie.mem_elementCentralizer_baseChange_affine_iff (Y : lieKernel G_E E)
    (g : Lie.AffinePoints G_E A) :
    g ∈ (Lie.elementCentralizer G_E Y).carrier
        ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E A))) ↔
      adjoint G A (Lie.affineBaseChangeEquiv k E G A g)
          (lieKernelMapLinear G (IsScalarTower.toAlgHom k E A)
            (Additive.ofMul (Lie.kernelBaseChangeEquiv k E G E Y))) =
        lieKernelMapLinear G (IsScalarTower.toAlgHom k E A)
          (Additive.ofMul (Lie.kernelBaseChangeEquiv k E G E Y)) := by
  rw [Lie.mem_elementCentralizer_adjoint_iff,
    ← (Lie.kernelBaseChangeLinearEquiv k E G A).injective.eq_iff,
    Lie.kernelBaseChangeLinearEquiv_adjoint, Lie.kernelBaseChangeLinearEquiv_naturality]
  rfl

end Transport

/-- Coefficient change on Lie vectors is compatible with composition. -/
theorem lieKernelMapLinear_comp {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
    [IsAffineHom G.X.hom] {A B C : Type u} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [CommRing C] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C)
    (x : Additive (lieKernel G A)) :
    lieKernelMapLinear G (g.comp f) x = lieKernelMapLinear G g (lieKernelMapLinear G f x) :=
  congrArg Additive.ofMul (lieKernelMap_comp G f g x.toMul)

section Conjugator

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T₀ : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The points of the all-test range of `j₀ : T₀ → G` fix the Lie element `Z` of `G` over a
`k`-algebra `Ω`: for every `k`-algebra `A`, every `k`-algebra map `ε : Ω → A` and every point
`s` of `G` over `A` in the range of `j₀`, the adjoint action of `s` fixes the image of `Z`
under `ε`. -/
def RangeFixesLieElement {Ω : Type u} [CommRing Ω] [Algebra k Ω] (j₀ : T₀.toGrp ⟶ G)
    (Z : lieKernel G Ω) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A] (ε : Ω →ₐ[k] A) (s : Lie.AffinePoints G A),
    s ∈ (SubgroupFunctor.range j₀).carrier
        ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))) →
      adjoint G A s (lieKernelMapLinear G ε (Additive.ofMul Z)) =
        lieKernelMapLinear G ε (Additive.ofMul Z)

/-- If the base change of `T₀` to a field `Ω` centralizes a Lie element `Z` of the base change
of `G`, then over every `Ω`-algebra the points of `T₀` fix the scalar extension of `Z`, read
in `G`. -/
theorem rangeFixesLieElement_of_range_le {Ω : Type u} [Field Ω] [Algebra k Ω]
    {j₀ : T₀.toGrp ⟶ G} (Z : lieKernel G Ω)
    (h : SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k Ω)).map j₀) ≤
      Lie.elementCentralizer ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj G)
        ((Lie.kernelBaseChangeEquiv k Ω G Ω).symm Z)) :
    RangeFixesLieElement j₀ Z := by
  intro A _ _ ε s hs
  let _ : Algebra Ω A := ε.toAlgebra
  have : IsScalarTower k Ω A := IsScalarTower.of_algebraMap_eq fun x => (ε.commutes x).symm
  have hs' : (Lie.affineBaseChangeEquiv k Ω G A).symm s ∈
      ((SubgroupFunctor.range j₀).baseChange (algebraBaseMap k Ω)).carrier
        ((algSpec (CommRingCat.of Ω)).obj (op (CommAlgCat.of Ω A))) := by
    rw [SubgroupFunctor.mem_baseChange_affine_iff, MulEquiv.apply_symm_apply]
    exact hs
  rw [← SubgroupFunctor.range_baseChangeHom] at hs'
  have hc := (Lie.mem_elementCentralizer_baseChange_affine_iff G _ _).1
    (SubgroupFunctor.le_def.1 h _ hs')
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hc
  have hε : IsScalarTower.toAlgHom k Ω A = ε := AlgHom.ext fun _ => rfl
  rwa [hε] at hc

variable {K Ω : Type u} [Field K] [Algebra k K] [Field Ω] [Algebra k Ω]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

/-- **A centralizer conjugator from a conjugation of Lie elements.** Let `ψ : K → Ω` be an
embedding over `k` into an algebraically closed field, `Y` a Lie element of `G` over `K`, and
`g` a point of `G` over `Ω` with dense image that conjugates a Lie element `Z` over `Ω` to the
scalar extension of `Y`. If over every `Ω`-algebra the points of `T₀` fix the scalar extension
of `Z`, then `g`, read as a point of the base change `G_K` over `Ω`, conjugates the base change
of `T₀` into the centralizer of `Y` in `G_K`. -/
theorem hasCentralizerConjugator_of_adjoint_eq [IsAlgClosed Ω] {j₀ : T₀.toGrp ⟶ G}
    (ψ : K →ₐ[k] Ω) (Y : lieKernel G K) (g : Lie.AffinePoints G Ω) (Z : lieKernel G Ω)
    (hgZ : adjoint G Ω g (Additive.ofMul Z) = lieKernelMapLinear G ψ (Additive.ofMul Y))
    (hZ : RangeFixesLieElement j₀ Z)
    (hg : DenseRange g.left) :
    HasCentralizerConjugator G j₀ ((Lie.kernelBaseChangeEquiv k K G K).symm Y) := by
  let _ : Algebra K Ω := ψ.toAlgebra
  have : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
  let c : Lie.AffinePoints G_K Ω := (Lie.affineBaseChangeEquiv k K G Ω).symm g
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, c, ?_, ?_⟩
  · have h₁ : (Lie.affineBaseChangeEquiv k K G Ω c).left =
        (baseChangePointsEquiv (algebraBaseMap k K) G (Over.mk (algebraBaseMap K Ω)) c).left :=
      Category.id_comp _
    rw [← h₁, MulEquiv.apply_symm_apply]
    exact hg
  intro V y t ht
  rw [Lie.mem_elementCentralizer]
  intro A _ _ a
  let _ : Algebra k A := ((algebraMap K A).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let a' : (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A)) ⟶
      (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K Ω)) := a ≫ y
  let ε' : Ω →ₐ[K] A := (algSpec.fullyFaithful.preimage a').unop.hom
  have hε' : (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom ε').op = a' :=
    algSpec.fullyFaithful.map_preimage a'
  let ε : Ω →ₐ[k] A := ε'.restrictScalars k
  suffices hmem : a ≫ ((y ≫ c) * t * (y ≫ c)⁻¹) ∈
      (Lie.elementCentralizer G_K ((Lie.kernelBaseChangeEquiv k K G K).symm Y)).carrier
        ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A))) by
    simpa only [Category.id_comp] using hmem A (𝟙 _)
  have hcomp : a ≫ ((y ≫ c) * t * (y ≫ c)⁻¹) =
      Lie.affineMap G_K ε' c * (a ≫ t) * (Lie.affineMap G_K ε' c)⁻¹ := by
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, Lie.affineMap_apply, hε']
    rfl
  rw [hcomp, Lie.mem_elementCentralizer_baseChange_affine_iff, MulEquiv.apply_symm_apply,
    map_mul (Lie.affineBaseChangeEquiv k K G A), map_mul (Lie.affineBaseChangeEquiv k K G A),
    map_inv, Lie.affineBaseChangeEquiv_naturality, MulEquiv.apply_symm_apply]
  have hψ : IsScalarTower.toAlgHom k K A = ε.comp ψ := AlgHom.ext fun x => (ε'.commutes x).symm
  have hY : lieKernelMapLinear G (IsScalarTower.toAlgHom k K A) (Additive.ofMul Y) =
      adjoint G A (Lie.affineMap G ε g) (lieKernelMapLinear G ε (Additive.ofMul Z)) := by
    rw [← adjoint_naturality, hgZ, hψ, lieKernelMapLinear_comp]
  have hs := hZ A ε _ ((SubgroupFunctor.mem_baseChange_affine_iff G _ _).1
    ((SubgroupFunctor.baseChange (algebraBaseMap k K) (SubgroupFunctor.range j₀)).comp_mem
      a ht))
  rw [hY]
  set gA := Lie.affineMap G ε g
  set s := Lie.affineBaseChangeEquiv k K G A (a ≫ t)
  set v := lieKernelMapLinear G ε (Additive.ofMul Z)
  calc adjoint G A (gA * s * gA⁻¹) (adjoint G A gA v) = adjoint G A (gA * s * gA⁻¹ * gA) v := by
        rw [map_mul _ _ gA]
        rfl
    _ = adjoint G A gA (adjoint G A s v) := by
        rw [inv_mul_cancel_right, map_mul]
        rfl
    _ = adjoint G A gA v := by rw [hs]

end Conjugator

end Langlands.GroupScheme
