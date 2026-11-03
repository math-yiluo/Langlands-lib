import Langlands.GroupScheme.SubgroupFunctor.FppfProduct
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Normality and leastness of represented fppf subgroup products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G P Q : GroupScheme S}

/-- Membership in a subgroup functor is fppf-local if it descends along
every flat, surjective, locally finitely presented relative test map. -/
def IsFppfLocal (A : SubgroupFunctor G) : Prop :=
  ∀ (T V : Over S) (v : V ⟶ T),
    Flat v.left → Surjective v.left → LocallyOfFinitePresentation v.left →
      ∀ x : T ⟶ G.X, v ≫ x ∈ A.carrier V → x ∈ A.carrier T

/-- The all-test image of a monomorphism has fppf-local membership. -/
theorem isFppfLocal_range (j : Q ⟶ G) [Mono j.hom.hom] :
    (range j).IsFppfLocal := by
  intro T V v hf hs hl x hx
  let : Flat v.left := hf
  let : Surjective v.left := hs
  let : LocallyOfFinitePresentation v.left := hl
  exact mem_range_of_comp_mem_range j v hx

namespace FppfLocallyInProduct

variable {F N : SubgroupFunctor G} {T : Over S} {x : T ⟶ G.X}

/-- Conjugation preserves fppf-local product membership when it preserves
both factors on every scheme test. -/
theorem conj (hx : FppfLocallyInProduct F N x)
    (hF : F.IsNormal) (hN : N.IsNormal) (g : T ⟶ G.X) :
    FppfLocallyInProduct F N (g * x * g⁻¹) := by
  obtain ⟨V, v, hf, hs, hl, p, n, hp, hn, he⟩ := hx
  refine ⟨V, v, hf, hs, hl,
    (v ≫ g) * p * (v ≫ g)⁻¹, (v ≫ g) * n * (v ≫ g)⁻¹,
    hF V (v ≫ g) p (Subgroup.mem_top _) hp,
    hN V (v ≫ g) n (Subgroup.mem_top _) hn, ?_⟩
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, he]
  simp only [mul_assoc, inv_mul_cancel_left]

/-- Local product membership implies membership in any fppf-local subgroup
functor containing both factors. -/
theorem mem_of_le (hx : FppfLocallyInProduct F N x)
    {A : SubgroupFunctor G} (hA : A.IsFppfLocal) (hF : F ≤ A) (hN : N ≤ A) :
    x ∈ A.carrier T := by
  obtain ⟨V, v, hf, hs, hl, p, n, hp, hn, he⟩ := hx
  apply hA T V v hf hs hl x
  rw [he]
  exact (A.carrier V).mul_mem (hF V hp) (hN V hn)

/-- Membership in a represented monic subgroup descends from the local
factorization when that subgroup contains both factors. -/
theorem mem_range_of_le (hx : FppfLocallyInProduct F N x)
    (j : Q ⟶ G) [Mono j.hom.hom] (hF : F ≤ range j) (hN : N ≤ range j) :
    x ∈ (range j).carrier T :=
  hx.mem_of_le (isFppfLocal_range j) hF hN

end FppfLocallyInProduct

namespace IsFppfProduct

variable {F N : SubgroupFunctor G} {i : P ⟶ G}

/-- The image of a supplied closed fppf-product representative has
fppf-local membership. -/
theorem isFppfLocal (hi : IsFppfProduct F N i) : (range i).IsFppfLocal := by
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  exact isFppfLocal_range i

/-- A represented fppf-local product of normal subgroup functors is normal
on every test scheme. -/
theorem isNormal (hi : IsFppfProduct F N i) (hF : F.IsNormal) (hN : N.IsNormal) :
    (range i).IsNormal := by
  intro T g x _ hx
  exact (hi.mem_range_iff T _).mpr
    (((hi.mem_range_iff T x).mp hx).conj hF hN g)

/-- The represented fppf-local product is contained in every fppf-local
subgroup functor containing its two factors. -/
theorem le_of_isFppfLocal (hi : IsFppfProduct F N i) {A : SubgroupFunctor G}
    (hA : A.IsFppfLocal) (hF : F ≤ A) (hN : N ≤ A) : range i ≤ A := by
  intro T x hx
  exact ((hi.mem_range_iff T x).mp hx).mem_of_le hA hF hN

/-- The represented fppf-local product is contained in every represented
monic subgroup containing its two factors. -/
theorem le_range (hi : IsFppfProduct F N i) (j : Q ⟶ G) [Mono j.hom.hom]
    (hF : F ≤ range j) (hN : N ≤ range j) : range i ≤ range j := by
  intro T x hx
  exact ((hi.mem_range_iff T x).mp hx).mem_range_of_le j hF hN

/-- Containment of a represented fppf-local product in a represented monic
subgroup is equivalent to containment of each factor. -/
theorem le_range_iff (hi : IsFppfProduct F N i) (j : Q ⟶ G) [Mono j.hom.hom] :
    range i ≤ range j ↔ F ≤ range j ∧ N ≤ range j :=
  ⟨fun h => ⟨le_trans hi.left_le h, le_trans hi.right_le h⟩,
    fun h => hi.le_range j h.1 h.2⟩

end IsFppfProduct

end Langlands.GroupScheme.SubgroupFunctor
