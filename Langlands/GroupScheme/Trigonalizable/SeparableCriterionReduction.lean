import Langlands.GroupScheme.Trigonalizable.UnipotentKernelMaximal
import Langlands.GroupScheme.Trigonalizable.CharacterizationStatement
import Langlands.GroupScheme.Trigonalizable.SeparableCriterionStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Torus.CentralExtensionSplit
import Langlands.GroupScheme.Trigonalizable.GreatestUnipotent
import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups
import Langlands.GroupScheme.Unipotent.FieldReflectionProof
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.AffineNormalSubgroupQuotientProof
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Milne 16.6 from Milne 16.2 -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SeparableTrigonalization

variable {k : Type u} [Field k]

/-- Milne 16.6, (b) ⇒ (a), assuming Milne 16.2: if `G` has a normal unipotent closed subgroup
with an fppf quotient onto a group of multiplicative type, then `G` becomes trigonalizable over a
finite Galois, hence separable, extension of `k`. -/
theorem exists_separable_isTrigonalizable
    (hChar : TrigonalizableCharacterizationStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    {U M : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ G) (q : G ⟶ M)
    (hi : IsClosedSubgroup i) (hU : IsUnipotent U) (hN : (SubgroupFunctor.range i).IsNormal)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hM : IsMultiplicativeType M) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), Algebra.IsSeparable k K ∧
      IsTrigonalizable
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) := by
  obtain ⟨K, _, _, _, _, Λ, _, _, ⟨e⟩⟩ := multiplicativeTypeFiniteGaloisSplitting k M hM
  refine ⟨K, inferInstance, inferInstance, inferInstance, ?_⟩
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  have : LocallyOfFiniteType (B.obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom (B.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom U.X.hom := hi.isAffineHom
  refine (hChar K (B.obj G)).2.2.2 ⟨B.obj U, B.map i, Λ, inferInstance, inferInstance,
    B.map q ≫ e.hom, hi.baseChange b, hU.baseChange, ?_, ?_⟩
  · rw [SubgroupFunctor.range_baseChangeHom]
    exact hN.baseChange b
  · rw [SubgroupFunctor.range_baseChangeHom]
    exact (hq.baseChange b).comp_iso e

/-- Milne 16.6, (a) ⇒ (b), assuming Milne 16.2: if `G` becomes trigonalizable over a separable
extension `K` of `k`, then `G` has a normal unipotent closed subgroup with an fppf quotient onto a
group of multiplicative type.

Milne 16.2 over `K` gives such a subgroup `U'` of `G_K` with diagonalizable quotient. Its base
change to a separable closure `Ω` of `k` (into which `K` embeds) is the greatest unipotent closed
subgroup of `G_Ω`, hence Galois invariant, so it descends to a closed subgroup `U` of `G`. Then
`U` is unipotent and normal because both properties descend, and the quotient `G/U` becomes
isomorphic over `Ω` to the diagonalizable quotient of `G_Ω`. -/
theorem exists_unipotent_multiplicativeType_quotient
    (hChar : TrigonalizableCharacterizationStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (K : Type u) [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (hT : IsTrigonalizable
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    ∃ (U M : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G) (q : G ⟶ M),
      IsClosedSubgroup i ∧ IsUnipotent U ∧ (SubgroupFunctor.range i).IsNormal ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧ IsMultiplicativeType M := by
  -- The data of Milne 16.2 (d) over `K`.
  let bK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : LocallyOfFiniteType ((GroupScheme.baseChange bK).obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom bK)
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange bK).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom bK)
    infer_instance
  obtain ⟨U', i', Λ, _, hfg, q', hi', hU', hN', hq'⟩ :=
    (hChar K ((GroupScheme.baseChange bK).obj G)).2.2.1 hT
  have : IsAffineHom U'.X.hom := hi'.isAffineHom
  -- Transport to the separable closure `Ω` of `k`, through an embedding `K → Ω`.
  let Ω := SeparableClosure k
  let f : K →ₐ[k] Ω := IsSepClosed.lift
  let : Algebra K Ω := f.toRingHom.toAlgebra
  have : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let c := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let b := algebraBaseMap k Ω
  let C := GroupScheme.baseChange c
  let B := GroupScheme.baseChange b
  let tower := baseChangeFieldTowerIso k K Ω G
  let d := Diagonalizable.baseChangeIso c Λ
  let i'' : C.obj U' ⟶ B.obj G := C.map i' ≫ tower.symm.hom
  let q'' : B.obj G ⟶ (Diagonalizable.groupScheme (CommRingCat.of Ω) Λ).toGrp :=
    tower.symm.inv ≫ (C.map q' ≫ d.hom)
  have hi'' : IsClosedSubgroup i'' := (hi'.baseChange c).comp_iso tower.symm
  have hU'' : IsUnipotent (C.obj U') := hU'.baseChange
  have hrange : SubgroupFunctor.range i'' =
      ((SubgroupFunctor.range i').baseChange c).comap tower.symm.inv := by
    rw [SubgroupFunctor.range_comp_iso, SubgroupFunctor.range_baseChangeHom]
  have hq'' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i'') q'' := by
    rw [hrange]
    exact ((hq'.baseChange c).comp_iso d).comapIso tower.symm
  have hN'' : (SubgroupFunctor.range i'').IsNormal := by
    rw [hrange]
    exact (hN'.baseChange c).comap _
  have : IsAffineHom (B.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have hM'' : IsMultiplicativeType (Diagonalizable.groupScheme (CommRingCat.of Ω) Λ).toGrp :=
    ⟨Ω, inferInstance, inferInstance, Λ, inferInstance, hfg,
      ⟨Diagonalizable.baseChangeIso _ Λ⟩⟩
  have hgreat : IsGreatestUnipotentSubgroup i'' :=
    IsUnipotent.isGreatestUnipotentSubgroup hi'' hU'' hq'' hM''
  -- Galois descent of the (unique, hence Galois-invariant) unipotent subgroup.
  obtain ⟨H₀, j₀, r, _, hj₀, hfac⟩ :=
    Descent.GaloisInvariantClosedSubgroup.exists_descent hi'' hgreat.range_radicalGaloisHom
  have : IsAffineHom H₀.X.hom := hj₀.isAffineHom
  have hrange₀ : (SubgroupFunctor.range j₀).baseChange b = SubgroupFunctor.range i'' := by
    rw [← SubgroupFunctor.range_baseChangeHom, hfac, SubgroupFunctor.range_iso_comp]
  have hH₀ : IsUnipotent H₀ := IsUnipotent.of_baseChange (K := Ω) (IsUnipotent.of_iso r hU'')
  obtain ⟨hs, hf, hqc⟩ := fieldExtension_fpqc k Ω
  have : IsClosedImmersion j₀.hom.hom.left := hj₀
  have : Mono j₀.hom.hom := Over.mono_of_mono_left _
  have hN₀ : (SubgroupFunctor.range j₀).IsNormal := by
    apply SubgroupFunctor.isNormal_range_of_baseChange b j₀
    rw [hrange₀]
    exact hN''
  -- The affine quotient by the descended subgroup is of multiplicative type.
  obtain ⟨M₀, q₀, _, _, hq₀⟩ := affineNormalSubgroupQuotient k G H₀ j₀ hj₀ hN₀
  refine ⟨H₀, M₀, j₀, q₀, hj₀, hH₀, hN₀, hq₀, ?_⟩
  have hq₀b : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i'') (B.map q₀) := by
    rw [← hrange₀]
    exact hq₀.baseChange b
  have : IsAffine (B.obj G).X.left := isAffine_of_isAffineHom (B.obj G).X.hom
  have : IsAffineHom (B.obj M₀).X.hom := by
    change IsAffineHom (pullback.snd M₀.X.hom b)
    infer_instance
  have : IsAffine (B.obj M₀).X.left := isAffine_of_isAffineHom (B.obj M₀).X.hom
  have : IsAffine (Diagonalizable.groupScheme (CommRingCat.of Ω) Λ).X.left :=
    isAffine_of_isAffineHom (Diagonalizable.groupScheme (CommRingCat.of Ω) Λ).X.hom
  have : IsAffineHom (B.map q₀).hom.hom.left := isAffineHom_of_isAffine _
  have : IsAffineHom q''.hom.hom.left := isAffineHom_of_isAffine _
  exact ⟨Ω, inferInstance, inferInstance, Λ, inferInstance, hfg,
    ⟨FppfQuotientComparison.iso hq₀b hq''⟩⟩

/-- Milne 16.6 from Milne 16.2: the published statement follows from the characterization of
trigonalizable groups. -/
theorem separablyTrigonalizableCriterion_of_characterization
    (hChar : TrigonalizableCharacterizationStatement.{u}) :
    SeparablyTrigonalizableCriterionStatement.{u} := by
  intro k _ G _ _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨K, _, _, _, hT⟩
    exact exists_unipotent_multiplicativeType_quotient hChar G K hT
  · rintro ⟨U, M, i, q, hi, hU, hN, hq, hM⟩
    exact exists_separable_isTrigonalizable hChar G i q hi hU hN hq hM
  · intro U M i q _ _ _ hq hM V j hj hV
    exact IsUnipotent.range_le_of_isFppfQuotient i q hq hM j hj hV

end SeparableTrigonalization

end Langlands.GroupScheme
