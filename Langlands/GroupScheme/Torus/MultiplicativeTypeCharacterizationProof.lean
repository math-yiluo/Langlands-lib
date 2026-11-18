import Langlands.GroupScheme.Torus.MultiplicativeTypeCharacterizationStatement
import Langlands.RingTheory.Coalgebra.CoetaleHopf
import Langlands.GroupScheme.Torus.MultiplicativeTypeAdditiveHom
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.AffineCoordinatesFiniteType

/-! # Proof: characterizations of groups of multiplicative type over a field (Milne 12.18) -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace MultiplicativeTypeCharacterization

/-- Commutativity transports along isomorphisms of group schemes. -/
theorem isCommMonObj_of_iso {S : Scheme.{u}} {G H : GroupScheme S} (e : G ≅ H)
    [IsCommMonObj H.X] : IsCommMonObj G.X := by
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro U
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (isoPointsEquiv e U).injective
  rw [map_mul, map_mul, mul_comm]

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))

/-- A group scheme that becomes diagonalizable after a field extension is commutative. -/
theorem isCommMonObj_of_diagonalizable {K : Type u} [Field K] [Algebra k K] {Λ : Type u}
    [AddCommGroup Λ]
    (e : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
      (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp) :
    IsCommMonObj G.X := by
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc k K
  have : IsCommMonObj
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X :=
    isCommMonObj_of_iso e
  exact isCommMonObj_of_baseChange _ G this

/-- A diagonalizable model after a field extension gives group-like spanning of the
scalar-extended coordinate Hopf algebra. -/
theorem span_of_diagonalizable [IsAffine G.X.left] {K : Type u} [Field K] [Algebra k K]
    {Λ : Type u} [AddCommGroup Λ]
    (e : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
      (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp) :
    Submodule.span K
      {a : K ⊗[k] AffineCoordinates.hopfAlgebra G | IsGroupLikeElem K a} = ⊤ :=
  SplittingAssembly.span_of_hopfSpecIso
    (HopfCoordinates.scalarExtension k K (AffineCoordinates.hopfAlgebra G))
    (Diagonalizable.hopfAlgebra (CommRingCat.of K) Λ)
    (SplittingAssembly.scalarExtensionCoordinatesIso G ≪≫ e ≪≫
      (Diagonalizable.hopfSpecIso (CommRingCat.of K) Λ).symm)
    AddMonoidAlgebra.span_isGroupLikeElem

/-- If the scalar-extended coordinate Hopf algebra of a group of finite type is spanned by
group-like elements, the base-changed group is diagonalizable with finitely generated character
group. -/
theorem diagonalizable_of_span [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (K : Type u) [Field K] [Algebra k K]
    (hspan : Submodule.span K
      {a : K ⊗[k] AffineCoordinates.hopfAlgebra G | IsGroupLikeElem K a} = ⊤) :
    ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
      Nonempty (((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) ≅
          (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp) := by
  let A := AffineCoordinates.hopfAlgebra G
  let M := GroupLike K (K ⊗[k] A)
  let eRec : (K ⊗[k] A) ≃ₐc[K] AddMonoidAlgebra K (Additive M) :=
    (Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike hspan).symm.trans
      (_root_.MonoidAlgebra.toAdditiveBialgEquiv K K M)
  have : Algebra.FiniteType k A := AffineCoordinates.algebraFiniteType G
  have hfin : Algebra.FiniteType K (AddMonoidAlgebra K (Additive M)) :=
    (inferInstance : Algebra.FiniteType K (K ⊗[k] A)).equiv eRec.toAlgEquiv
  refine ⟨Additive M, inferInstance, AddMonoidAlgebra.finiteType_iff_group_fg.mp hfin, ⟨?_⟩⟩
  let i : HopfCoordinates.scalarExtension k K A ≅
      Diagonalizable.hopfAlgebra (CommRingCat.of K) (Additive M) :=
    CommHopfAlgCat.isoMk eRec
  exact (SplittingAssembly.scalarExtensionCoordinatesIso G).symm ≪≫
    ((hopfSpec (CommRingCat.of K)).mapIso i.op).symm ≪≫
      Diagonalizable.hopfSpecIso (CommRingCat.of K) (Additive M)

end MultiplicativeTypeCharacterization

open MultiplicativeTypeCharacterization in
/-- **Milne, Theorem 12.18.** For an affine group scheme of finite type over a field `k` and a
separable closure `Ks` of `k`, being of multiplicative type, being commutative without
nontrivial homomorphisms to `𝔾ₐ`, being commutative with coétale coordinate coalgebra, and
becoming diagonalizable over `Ks` are equivalent. -/
theorem multiplicativeTypeCharacterization : MultiplicativeTypeCharacterizationStatement.{u} := by
  intro k _ G _ _ Ks _ _ _
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsSepClosed Ks := IsSepClosure.sep_closed k
  have : Algebra.IsAlgebraic k Ks := (IsSepClosure.separable (k := k) (K := Ks)).isAlgebraic
  tfae_have 1 → 4 := fun hG =>
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed _
      (MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic k Ks G hG)
  tfae_have 4 → 1 := fun ⟨Λ, hΛ, hfg, he⟩ => ⟨Ks, inferInstance, inferInstance, Λ, hΛ, hfg, he⟩
  tfae_have 4 → 2 := by
    rintro ⟨Λ, hΛ, hfg, ⟨e⟩⟩
    refine ⟨isCommMonObj_of_diagonalizable G e, subsingleton_of_noPrimitive G fun a ha => ?_⟩
    exact Langlands.CoetaleHopf.eq_zero_of_isPrimitiveElem_of_span_baseChange
      Ks (span_of_diagonalizable G e) a ha
  tfae_have 2 → 3 := by
    rintro ⟨hc, hs⟩
    refine ⟨hc, fun c => ?_⟩
    have : Coalgebra.IsCocomm k (AffineCoordinates.hopfAlgebra G) :=
      AffineCoordinates.hopfAlgebra_isCocomm G
    obtain ⟨D, hcD, hfin⟩ := Subcoalgebra.localFiniteness k (AffineCoordinates.hopfAlgebra G) c
    have hD : Coalgebra.IsCocomm k D :=
      Langlands.CoetaleHopf.isCocomm_subcoalgebra D
    exact ⟨D, hcD, hfin, hD, Langlands.CoetaleHopf.etale_of_noPrimitive
      (eq_zero_of_isPrimitiveElem_of_subsingleton G hs) D⟩
  tfae_have 3 → 4 := by
    rintro ⟨_, h⟩
    exact diagonalizable_of_span G Ks
      (Langlands.CoetaleHopf.span_baseChange_of_coetale Ks h)
  tfae_finish

end Langlands.GroupScheme
