import Langlands.GroupScheme.Trigonalizable.FiniteEtaleMorphisms
import Langlands.GroupScheme.Trigonalizable.FiniteGroupAveraging
import Langlands.GroupScheme.GaloisPointDescent
import Langlands.GroupScheme.Rational.VectorGroupSplit
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.GroupScheme.SplitUnipotentQuotientSection

/-! # Splitting a vector extension over an affine étale quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.EtaleExtensionSplit

set_option backward.isDefEq.respectTransparency false

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

private def conjugation (G : GroupScheme (Spec (CommRingCat.of k))) (σ : L ≃ₐ[k] L) :
    (geometricTest k L ⟶ G.X) ≃* (geometricTest k L ⟶ G.X) where
  toFun := GaloisPoint.conjugate k L G σ
  invFun := GaloisPoint.conjugate k L G σ⁻¹
  left_inv x := by
    rw [← GaloisPoint.conjugate_mul, inv_mul_cancel, GaloisPoint.conjugate_one]
  right_inv x := by
    rw [← GaloisPoint.conjugate_mul, mul_inv_cancel, GaloisPoint.conjugate_one]
  map_mul' := map_mul (GaloisPoint.conjugate k L G σ)

private theorem point_mul {T : Over (Spec (CommRingCat.of k))}
    (G : GroupScheme (Spec (CommRingCat.of k))) (x : T ⟶ G.X ⊗ G.X) :
    x ≫ μ[G.X] = (x ≫ fst _ _) * (x ≫ snd _ _) := by
  change x ≫ μ[G.X] = lift (x ≫ fst _ _) (x ≫ snd _ _) ≫ μ[G.X]
  rw [← comp_lift, lift_fst_snd, Category.comp_id]

private theorem exists_section_of_equivariant_points [IsSepClosed L] [IsGalois k L]
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
    [IsAffineHom H.X.hom] [Etale H.X.hom] (f : G ⟶ H)
    (t : (geometricTest k L ⟶ H.X) →* (geometricTest k L ⟶ G.X))
    (ht : ∀ x, t x ≫ f.hom.hom = x)
    (hc : ∀ (σ : L ≃ₐ[k] L) x, t (conjugationTest σ ≫ x) = conjugationTest σ ≫ t x) :
    ∃ s : H ⟶ G, s ≫ f = 𝟙 H := by
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨s, hs⟩ := exists_hom_of_equivariant t hc
  have hone : η[H.X] ≫ s = η[G.X] := by
    let : IsAffine (𝟙_ (Over (Spec (CommRingCat.of k)))).left := by
      change IsAffine (Spec (CommRingCat.of k))
      infer_instance
    let : Etale (𝟙_ (Over (Spec (CommRingCat.of k)))).hom := by
      change Etale (𝟙 (Spec (CommRingCat.of k)))
      infer_instance
    apply geometric_hom_ext (L := L)
    intro x
    rw [← Category.assoc, hs]
    have hx : x = toUnit (geometricTest k L) := toUnit_unique _ _
    rw [hx]
    exact map_one t
  have hmul : μ[H.X] ≫ s = (s ⊗ₘ s) ≫ μ[G.X] := by
    let pb := IsPullback.of_hasPullback H.X.hom H.X.hom
    let : IsAffineHom (pullback.fst H.X.hom H.X.hom) :=
      MorphismProperty.of_isPullback pb.flip inferInstance
    let : Etale (pullback.fst H.X.hom H.X.hom) :=
      MorphismProperty.of_isPullback pb.flip inferInstance
    let : IsAffineHom (H.X ⊗ H.X).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    let : IsAffine (H.X ⊗ H.X).left := isAffine_of_isAffineHom (H.X ⊗ H.X).hom
    let : Etale (H.X ⊗ H.X).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    apply geometric_hom_ext (L := L)
    intro x
    rw [← Category.assoc, hs, point_mul, map_mul, ← Category.assoc, point_mul]
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd, ← hs]
  refine ⟨Grp.homMk'' s hone hmul, ?_⟩
  apply (Grp.forget _).map_injective
  change s ≫ f.hom.hom = 𝟙 H.X
  apply geometric_hom_ext (L := L)
  intro x
  rw [← Category.assoc, hs, ht, Category.comp_id]

/-- Over a field of characteristic `p > 1`, an extension of an affine étale
quotient of prime-to-`p` geometric order by a vector group admits a group section. -/
theorem exists_section_of_vector_kernel [IsSepClosed L] [IsGalois k L]
    (p : ℕ) [CharP L p] (hp : 1 < p)
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [IsAffineHom H.X.hom] [Etale H.X.hom]
    (hcard : (Nat.card (geometricTest k L ⟶ H.X)).Coprime p)
    (f : G ⟶ H) [Smooth f.hom.hom.left] [Surjective f.hom.hom.left] {n : ℕ}
    (hv : RelativeRoot.IsVectorGroupOfDimension (kernel f) n) :
    ∃ s : H ⟶ G, s ≫ f = 𝟙 H := by
  classical
  let T := geometricTest k L
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : Smooth (kernel f).X.hom := hv.smooth
  have hf : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) f :=
    ⟨inferInstance, inferInstance, inferInstance, rfl⟩
  obtain ⟨s₀, hs₀⟩ := HomogeneousQuotient.fppf_section_of_split_unipotent_torsors
    G (kernel f) (kernelι f) splitUnipotentAffineTorsorStatement
    (show IsClosedImmersion (kernelι f).hom.hom.left from inferInstance)
    hv.isSplitUnipotent H f hf
  let F : (T ⟶ G.X) →* (T ⟶ H.X) := ((yonedaGrp.map f).app (op T)).hom
  have hF (x : T ⟶ G.X) : F x = x ≫ f.hom.hom := rfl
  let s (x : T ⟶ H.X) := x ≫ s₀
  have hs (x : T ⟶ H.X) : F (s x) = x := by
    rw [hF]
    change (x ≫ s₀) ≫ f.hom.hom = x
    rw [Category.assoc, hs₀, Category.comp_id]
  obtain ⟨e, _⟩ := hv
  let eK : F.ker ≃* Multiplicative (Fin n → Γ(T.left, ⊤)) :=
    (kernelPointsEquiv f T).symm.trans (e T)
  let : IsMulCommutative F.ker := ⟨⟨fun x y => eK.injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩
  have hK (x : F.ker) : x ^ p = 1 := by
    apply eK.injective
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    funext i
    change p • (eK x).toAdd i = 0
    let ρ := (Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv
    apply ρ.injective
    change ρ (p • (eK x).toAdd i) = ρ 0
    rw [map_nsmul, map_zero, nsmul_eq_mul, CharP.cast_eq_zero L p, zero_mul]
  let : Finite (T ⟶ H.X) := EtaleMultiplicativeTypeOrder.finite_points k L H.X
  let : Fintype (T ⟶ H.X) := Fintype.ofFinite _
  have hq : (Fintype.card (T ⟶ H.X)).Coprime p := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨t, ht, hc⟩ := exists_equivariant_averaged_section F s hs p hp hq hK
    (conjugation G) (conjugation H)
    (fun σ x => Category.assoc (conjugationTest σ) x f.hom.hom)
    (fun σ x => Category.assoc (conjugationTest σ) x s₀)
  exact exists_section_of_equivariant_points f t (fun x => ht x) (fun σ x => hc σ x)

end Langlands.GroupScheme.EtaleExtensionSplit
