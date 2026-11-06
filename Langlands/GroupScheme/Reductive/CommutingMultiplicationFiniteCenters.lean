import Langlands.GroupScheme.Reductive.CommutingMultiplicationIsogeny
import Langlands.GroupScheme.Reductive.ProductCenter
import Langlands.GroupScheme.CentralIsogeny.SemisimpleTransfer
import Langlands.GroupScheme.SmoothProducts

/-! # Commuting multiplication with finite factor centres -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {H K G : GroupScheme S}

/-- With separated target, the full kernel of multiplication of two closed
commuting subgroups with finite full centres is finite over the base. -/
theorem kernel_commutingSubgroupMultiplicationHom_isFinite
    [IsSeparated G.X.hom]
    (j : H ⟶ G) (i : K ⟶ G) (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup i)
    (hc : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hH : HasFiniteCenter H) (hK : HasFiniteCenter K) :
    IsFinite (kernel (commutingSubgroupMultiplicationHom j i hc)).X.hom := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact isFinite_of_isClosedSubgroup_of_isCentral_of_hasFiniteCenter
    (kernelι (commutingSubgroupMultiplicationHom j i hc))
    (show IsClosedImmersion
      (kernelι (commutingSubgroupMultiplicationHom j i hc)).hom.hom.left from inferInstance)
    (isCentral_kernelι_commutingSubgroupMultiplicationHom j i hc) (hH.tensor hK)

end Base

section Field

variable {k : Type u} [Field k]
variable {H K G : GroupScheme (Spec (CommRingCat.of k))}

/-- Surjective multiplication of closed commuting subgroups with finite full
centres in a smooth affine field group is an actual central isogeny. -/
theorem isCentralIsogeny_commutingSubgroupMultiplicationHom_of_finite_centers
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (j : H ⟶ G) (i : K ⟶ G) (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup i)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hs : Surjective (subgroupMultiplication j i).left)
    (hH : HasFiniteCenter H) (hK : HasFiniteCenter K) :
    IsCentralIsogeny (commutingSubgroupMultiplicationHom j i hc) :=
  isCentralIsogeny_commutingSubgroupMultiplicationHom_of_finite_kernel j i hj hi hc hs
    (kernel_commutingSubgroupMultiplicationHom_isFinite j i hj hi hc hH hK)

/-- If the ambient group is semisimple, smooth connected commuting factors
with finite full centres and surjective multiplication have semisimple product. -/
theorem isSemisimple_tensor_of_commutingSubgroupMultiplication
    (j : H ⟶ G) (i : K ⟶ G) (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup i)
    (hG : IsSemisimple G)
    (hHs : Smooth H.X.hom) (hHc : ConnectedSpace H.X.left)
    (hKs : Smooth K.X.hom) (hKc : ConnectedSpace K.X.left)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hs : Surjective (subgroupMultiplication j i).left)
    (hH : HasFiniteCenter H) (hK : HasFiniteCenter K) : IsSemisimple (H ⊗ K) := by
  have : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  have : Smooth G.X.hom := hG.isConnectedReductive.smooth
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion i.hom.hom.left := hi
  have hHa : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have hKa : IsAffineHom K.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  apply IsSemisimple.of_isCentralIsogeny (commutingSubgroupMultiplicationHom j i hc)
    (isCentralIsogeny_commutingSubgroupMultiplicationHom_of_finite_centers
      j i hj hi hc hs hH hK) hG
  · exact smooth_tensor H.X K.X hHs hKs
  · have hgeom := smoothConnectedAffineGeometry.2 k H K hHs hHa hHc hKs hKa hKc
    have : GeometricallyIntegral (H ⊗ K).X.hom := hgeom.2.2.2
    have : Subsingleton (Spec (CommRingCat.of k)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have : IrreducibleSpace (H ⊗ K).X.left :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton (H ⊗ K).X.hom
    infer_instance

/-- The actual multiplication, together with its central-isogeny property and
the semisimplicity of its actual product source. -/
def semisimpleCommutingMultiplication
    (j : H ⟶ G) (i : K ⟶ G) (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup i)
    (hG : IsSemisimple G)
    (hHs : Smooth H.X.hom) (hHc : ConnectedSpace H.X.left)
    (hKs : Smooth K.X.hom) (hKc : ConnectedSpace K.X.left)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hs : Surjective (subgroupMultiplication j i).left)
    (hH : HasFiniteCenter H) (hK : HasFiniteCenter K) :
    { f : H ⊗ K ⟶ G // IsCentralIsogeny f ∧ IsSemisimple (H ⊗ K) } := by
  have : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  have : Smooth G.X.hom := hG.isConnectedReductive.smooth
  exact ⟨commutingSubgroupMultiplicationHom j i hc,
    isCentralIsogeny_commutingSubgroupMultiplicationHom_of_finite_centers
      j i hj hi hc hs hH hK,
    isSemisimple_tensor_of_commutingSubgroupMultiplication
      j i hj hi hG hHs hHc hKs hKc hc hs hH hK⟩

@[simp]
theorem semisimpleCommutingMultiplication_val
    (j : H ⟶ G) (i : K ⟶ G) (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup i)
    (hG : IsSemisimple G)
    (hHs : Smooth H.X.hom) (hHc : ConnectedSpace H.X.left)
    (hKs : Smooth K.X.hom) (hKc : ConnectedSpace K.X.left)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hs : Surjective (subgroupMultiplication j i).left)
    (hH : HasFiniteCenter H) (hK : HasFiniteCenter K) :
    (semisimpleCommutingMultiplication j i hj hi hG hHs hHc hKs hKc hc hs hH hK).val =
      commutingSubgroupMultiplicationHom j i hc := rfl

end Field

end Langlands.GroupScheme
