import Langlands.GroupScheme.FieldPoints
import Langlands.Algebra.UnitCocycleSemilocal
import Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityStatement
import Langlands.GroupScheme.Torus.InducedWeilDecompositionProof
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Proof: point surjectivity of quotients by induced central tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace InducedQuotientPointSurjectivity

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]
  {H G : GroupScheme (Spec (CommRingCat.of k))}

/-- Restricting points along an algebra map commutes with postcomposition by a homomorphism. -/
theorem affineMap_comp_hom (p : H ⟶ G) {A : Type u} [CommRing A] [Algebra k A]
    {T : Type u} [CommRing T] [Algebra k T] (φ : A →ₐ[k] T) (x : Lie.AffinePoints H A) :
    Lie.affineMap H φ x ≫ p.hom.hom = Lie.affineMap G φ (x ≫ p.hom.hom) := by
  simp only [Lie.affineMap_apply, Category.assoc]

/-- Postcomposition by a homomorphism on points is multiplicative. -/
theorem mul_inv_comp_hom (p : H ⟶ G) {A : Type u} [CommRing A] [Algebra k A]
    (x y : Lie.AffinePoints H A) :
    (x * y⁻¹) ≫ p.hom.hom = (x ≫ p.hom.hom) * (y ≫ p.hom.hom)⁻¹ := by
  change H.affinePointsTarget p (CommAlgCat.of k A) (x * y⁻¹) =
    H.affinePointsTarget p (CommAlgCat.of k A) x * (H.affinePointsTarget p (CommAlgCat.of k A) y)⁻¹
  rw [map_mul, map_inv]

/-- Rational-point surjectivity from a units model of the kernel. Suppose the kernel of
`p : H ⟶ G` on every affine test `T` is the image of an injective, natural homomorphism
`ψ_T : (B ⊗[k] T)ˣ → H(T)`, with `B` finite over `k`, and `p` is surjective on underlying
schemes. Then `H(K) → G(K)` is surjective for every field extension `K/k`. -/
theorem surjective_of_unitsKernel [Module.Finite k B] (K : Type u) [Field K] [Algebra k K]
    (p : H ⟶ G) (hp : Surjective p.hom.hom.left)
    (ψ : ∀ (T : Type u) [CommRing T] [Algebra k T], (B ⊗[k] T)ˣ →* Lie.AffinePoints H T)
    (hinj : ∀ (T : Type u) [CommRing T] [Algebra k T], Function.Injective (ψ T))
    (hnat : ∀ (T : Type u) [CommRing T] [Algebra k T] (T' : Type u) [CommRing T'] [Algebra k T']
      (φ : T →ₐ[k] T') (v : (B ⊗[k] T)ˣ),
      ψ T' (Units.map (Algebra.TensorProduct.map (AlgHom.id k B) φ : B ⊗[k] T →* B ⊗[k] T') v) =
        Lie.affineMap H φ (ψ T v))
    (hker : ∀ (T : Type u) [CommRing T] [Algebra k T] (x : Lie.AffinePoints H T),
      x ≫ p.hom.hom = 1 → ∃ v, ψ T v = x)
    (hcomp : ∀ (T : Type u) [CommRing T] [Algebra k T] (v : (B ⊗[k] T)ˣ),
      ψ T v ≫ p.hom.hom = 1) :
    Function.Surjective (H.affinePointsTarget p (CommAlgCat.of k K)) := by
  classical
  intro g
  obtain ⟨L, _, _, _, _, h1, hh1⟩ := FieldPoints.exists_field_lift p hp g
  let incl := IsScalarTower.toAlgHom k K L
  have hdiff : ∀ (T : Type u) [CommRing T] [Algebra k T] (a b : L →ₐ[k] T),
      a.comp incl = b.comp incl →
        ∃ v, ψ T v = Lie.affineMap H b h1 * (Lie.affineMap H a h1)⁻¹ := by
    intro T _ _ a b hab
    apply hker
    rw [mul_inv_comp_hom, affineMap_comp_hom, affineMap_comp_hom, hh1, ← Lie.affineMap_comp,
      ← Lie.affineMap_comp, hab, mul_inv_cancel]
  let c : ∀ (T : Type u) [CommRing T] [Algebra k T], (L →ₐ[k] T) → (L →ₐ[k] T) →
      (B ⊗[k] T)ˣ := fun T _ _ a b =>
    if hab : a.comp incl = b.comp incl then (hdiff T a b hab).choose else 1
  have hc : ∀ (T : Type u) [CommRing T] [Algebra k T] (a b : L →ₐ[k] T),
      a.comp incl = b.comp incl →
        ψ T (c T a b) = Lie.affineMap H b h1 * (Lie.affineMap H a h1)⁻¹ := by
    intro T _ _ a b hab
    have hcab : c T a b = (hdiff T a b hab).choose := by
      simp only [c]
      split_ifs
      rfl
    rw [hcab]
    exact (hdiff T a b hab).choose_spec
  have hcnat : ∀ (T : Type u) [CommRing T] [Algebra k T] (T' : Type u) [CommRing T']
      [Algebra k T'] (φ : T →ₐ[k] T') (a b : L →ₐ[k] T), a.comp incl = b.comp incl →
      c T' (φ.comp a) (φ.comp b) =
        Units.map (Algebra.TensorProduct.map (AlgHom.id k B) φ : B ⊗[k] T →* B ⊗[k] T')
          (c T a b) := by
    intro T _ _ T' _ _ φ a b hab
    have hab' : (φ.comp a).comp incl = (φ.comp b).comp incl := by
      rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hab]
    apply hinj T'
    rw [hnat, hc T a b hab, hc T' _ _ hab', map_mul, map_inv, Lie.affineMap_comp,
      Lie.affineMap_comp]
  have hcoc : ∀ (T : Type u) [CommRing T] [Algebra k T] (a b d : L →ₐ[k] T),
      a.comp incl = b.comp incl → b.comp incl = d.comp incl → c T a d = c T a b * c T b d := by
    intro T _ _ a b d hab hbd
    apply hinj T
    rw [mul_comm (c T a b), map_mul, hc T a d (hab.trans hbd), hc T a b hab, hc T b d hbd]
    group
  obtain ⟨f, hf⟩ := Algebra.Semilocal.exists_unit_coboundary (K := K) c hcnat hcoc
  let F := ψ L f
  let h2 := F⁻¹ * h1
  let a := (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] L).restrictScalars k
  let b := (Algebra.TensorProduct.includeRight : L →ₐ[K] L ⊗[K] L).restrictScalars k
  have hab : a.comp incl = b.comp incl := by
    ext x
    simp only [AlgHom.comp_apply, a, b, incl, AlgHom.restrictScalars_apply,
      IsScalarTower.coe_toAlgHom', AlgHom.commutes]
  have e : Lie.affineMap H b h1 * (Lie.affineMap H a h1)⁻¹ * Lie.affineMap H a F =
      Lie.affineMap H b F := by
    have := congrArg (ψ (L ⊗[K] L)) (hf (L ⊗[K] L) a b hab)
    rwa [map_mul, hc _ a b hab, hnat, hnat] at this
  have hdesc : Lie.affineMap H a h2 = Lie.affineMap H b h2 := by
    simp only [h2, map_mul, map_inv]
    rw [← e]
    group
  obtain ⟨y, hy⟩ := FieldPoints.exists_affineMap_eq H h2 hdesc
  refine ⟨y, FieldPoints.affineMap_injective (L := L) G ?_⟩
  change Lie.affineMap G incl (y ≫ p.hom.hom) = Lie.affineMap G incl g
  rw [← affineMap_comp_hom, hy, ← hh1]
  change H.affinePointsTarget p (CommAlgCat.of k L) (F⁻¹ * h1) =
    H.affinePointsTarget p (CommAlgCat.of k L) h1
  rw [map_mul, map_inv]
  rw [show H.affinePointsTarget p (CommAlgCat.of k L) F = 1 from hcomp L f, inv_one, one_mul]

section Weil

variable [Module.Finite k B] [Module.Projective k B]

omit [Module.Finite k B] [Module.Projective k B] in
/-- `lTensor` and `map id` agree as functions on `B ⊗[k] T`. -/
theorem lTensor_apply_eq_map {T T' : Type u} [CommRing T] [Algebra k T] [CommRing T']
    [Algebra k T'] (φ : T →ₐ[k] T') (x : B ⊗[k] T) :
    Algebra.TensorProduct.lTensor (S := B) B φ x =
      Algebra.TensorProduct.map (AlgHom.id k B) φ x := by
  induction x using TensorProduct.inductionOn with
  | tmul b t => simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (k B) in
/-- Points of `R_{B/k} 𝔾ₘ` over an affine test `T` are the units of `B ⊗[k] T`. -/
def weilPointsEquiv (T : Type u) [CommRing T] [Algebra k T] :
    Lie.AffinePoints (WeilGm.groupScheme (CommRingCat.of k) B) T ≃* (B ⊗[k] T)ˣ :=
  Corepresented.affinePointsEquiv (WeilGm.functor (CommRingCat.of k) B)
    (WeilGm.corepresentableBy (CommRingCat.of k) B) (CommAlgCat.of k T)

/-- The units model of Weil-restriction points is natural in the test algebra. -/
theorem weilPointsEquiv_affineMap {T T' : Type u} [CommRing T] [Algebra k T] [CommRing T']
    [Algebra k T'] (φ : T →ₐ[k] T')
    (x : Lie.AffinePoints (WeilGm.groupScheme (CommRingCat.of k) B) T) :
    weilPointsEquiv k B T' (Lie.affineMap _ φ x) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id k B) φ : B ⊗[k] T →* B ⊗[k] T')
        (weilPointsEquiv k B T x) := by
  have hn := Corepresented.affinePointsEquiv_naturality (WeilGm.functor (CommRingCat.of k) B)
    (WeilGm.corepresentableBy (CommRingCat.of k) B) (CommAlgCat.ofHom φ) x
  refine hn.trans ?_
  apply Units.ext
  exact lTensor_apply_eq_map φ _

/-- Rational-point surjectivity for a quotient by a closed subgroup isomorphic to a Weil
restriction `R_{B/k} 𝔾ₘ` of a finite `k`-algebra `B`. -/
theorem surjective_of_weil (K : Type u) [Field K] [Algebra k K]
    {Z : CommGroupScheme (Spec (CommRingCat.of k))}
    (e : Z ≅ WeilGm.commGroupScheme (CommRingCat.of k) B) (i : Z.toGrp ⟶ H) (p : H ⟶ G)
    (hcl : IsClosedSubgroup i) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p) :
    Function.Surjective (H.affinePointsTarget p (CommAlgCat.of k K)) := by
  let W := WeilGm.groupScheme (CommRingCat.of k) B
  let ei : W.X ⟶ Z.X := (CommGroupScheme.groupHom e.inv).hom.hom
  let eh : Z.X ⟶ W.X := (CommGroupScheme.groupHom e.hom).hom.hom
  have heh : eh ≫ ei = 𝟙 _ :=
    congrArg (fun f => (CommGroupScheme.groupHom f).hom.hom) e.hom_inv_id
  have hhe : ei ≫ eh = 𝟙 _ :=
    congrArg (fun f => (CommGroupScheme.groupHom f).hom.hom) e.inv_hom_id
  have : Mono i.hom.hom := hcl.mono_overHom
  let ψ : ∀ (T : Type u) [CommRing T] [Algebra k T], (B ⊗[k] T)ˣ →* Lie.AffinePoints H T :=
    fun T _ _ => (GroupScheme.affinePointsTarget Z.toGrp i (CommAlgCat.of k T)).comp
      ((GroupScheme.affinePointsTarget W (CommGroupScheme.groupHom e.inv)
        (CommAlgCat.of k T)).comp (weilPointsEquiv k B T).symm.toMonoidHom)
  have hψ : ∀ (T : Type u) [CommRing T] [Algebra k T] (v : (B ⊗[k] T)ˣ),
      ψ T v = ((weilPointsEquiv k B T).symm v ≫ ei) ≫ i.hom.hom := fun _ _ _ _ => rfl
  apply surjective_of_unitsKernel K p hq.2.1 ψ
  · intro T _ _ u v huv
    rw [hψ, hψ] at huv
    have h1 := (cancel_mono i.hom.hom).1 huv
    have h2 : (weilPointsEquiv k B T).symm u = (weilPointsEquiv k B T).symm v := by
      rw [← Category.comp_id ((weilPointsEquiv k B T).symm u),
        ← Category.comp_id ((weilPointsEquiv k B T).symm v), ← hhe, ← Category.assoc, h1,
        Category.assoc]
    exact (weilPointsEquiv k B T).symm.injective h2
  · intro T _ _ T' _ _ φ v
    have key : (weilPointsEquiv k B T').symm
        (Units.map (Algebra.TensorProduct.map (AlgHom.id k B) φ : B ⊗[k] T →* B ⊗[k] T') v) =
          Lie.affineMap W φ ((weilPointsEquiv k B T).symm v) := by
      rw [MulEquiv.symm_apply_eq, weilPointsEquiv_affineMap, MulEquiv.apply_symm_apply]
    rw [hψ, hψ, key]
    simp only [Lie.affineMap_apply, Category.assoc]
  · intro T _ _ x hx
    have hmem : x ∈ (SubgroupFunctor.range (kernelι p)).carrier
        ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k T))) :=
      (mem_range_kernelι_iff p x).2 hx
    rw [hq.2.2.2] at hmem
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hmem
    refine ⟨weilPointsEquiv k B T (z ≫ eh), ?_⟩
    rw [hψ, MulEquiv.symm_apply_apply, Category.assoc z eh ei, heh, Category.comp_id, hz]
  · intro T _ _ v
    have hmem : ψ T v ∈ (SubgroupFunctor.range i).carrier
        ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k T))) :=
      SubgroupFunctor.mem_range.2 ⟨_, (hψ T v).symm⟩
    rw [← hq.2.2.2] at hmem
    exact (mem_range_kernelι_iff p _).1 hmem

end Weil

end InducedQuotientPointSurjectivity

open InducedQuotientPointSurjectivity in
/-- **Point surjectivity of quotients by induced central tori.** For a field `k`, a field
extension `K/k`, an induced torus `Z` embedded as a closed subgroup `i : Z ⟶ H`, and an fppf
quotient `p : H ⟶ G` whose kernel is the image of `i`, the map `H(K) → G(K)` is surjective.
The reductivity and centrality hypotheses are not used. -/
theorem inducedTorusQuotientPointSurjectivity :
    InducedTorusQuotientPointSurjectivityStatement.{u} := by
  intro k _ K _ _ Z H G i p hind hcl _ _ _ hq
  obtain ⟨E, _, _, _, _, hsplit, -⟩ := id hind
  obtain ⟨n, F, ⟨e⟩⟩ := inducedTorusWeilDecomposition k E Z hsplit hind
  exact surjective_of_weil K e i p hcl hq

end Langlands.GroupScheme
