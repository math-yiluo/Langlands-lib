import Langlands.GroupScheme.Rational.CharactersStatement
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.SplitComponent.SchemeBridge

/-! # Existence and uniqueness of the split component

Over every field `k`, every affine group scheme `G` of finite type over `k` has a largest central
split torus: a central closed split subtorus `j : 𝔾_m^J ⟶ G` through which every central
homomorphism from a split torus factors. It is a split component, and every split component is
isomorphic to it over `G`. This proves `SplitComponentStatement`; only affineness and finite type
of a connected reductive group are used.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open SplitComponent Corepresented

section Lemmas

variable {S : Scheme.{u}} {H G G' K : GroupScheme S}

/-- A closed subgroup is a monomorphism of group schemes. -/
private theorem IsClosedSubgroup.cancel {i : H ⟶ G} (hi : IsClosedSubgroup i) {f g : K ⟶ H}
    (h : f ≫ i = g ≫ i) : f = g := by
  have : IsClosedImmersion i.hom.hom.left := hi
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  have h' := congrArg (fun q : K ⟶ G => q.hom.hom.left) h
  exact (cancel_mono i.hom.hom.left).mp h'

end Lemmas

section Field

variable {k : Type u} [Field k]

/-- The coordinate algebra of an affine group scheme locally of finite type over `k` is of
finite type. -/
theorem finiteType_coordinateAlgebra (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    Algebra.FiniteType (CommRingCat.of k) (AffineCoordinates.algebra G) := by
  let f := (AffineCoordinates.groupSchemeIso G).hom.hom.hom
  have : IsIso f.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso
      ((Grp.forget _).mapIso (AffineCoordinates.groupSchemeIso G))).hom)
  have h : LocallyOfFiniteType
      (groupScheme (AffineCoordinates.functor G) (AffineCoordinates.corepresentation G)).X.hom := by
    rw [← Over.w f]
    infer_instance
  have h' : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap (CommRingCat.of k) (AffineCoordinates.algebra G)))) := h
  exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h')

/-- **The largest central split torus.** An affine group scheme `G` over a field whose coordinate
algebra is of finite type has a central split subtorus `j : B ⟶ G` through which every central
homomorphism from a split torus factors. -/
theorem exists_largestCentralSplitTorus (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left]
    (hfin : Algebra.FiniteType (CommRingCat.of k) (AffineCoordinates.algebra G)) :
    ∃ (B : CommGroupScheme (Spec (CommRingCat.of k))) (j : B.toGrp ⟶ G),
      IsCentralSplitTorus j ∧
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (i : A.toGrp ⟶ G),
        IsSplitTorus A.toGrp → IsCentral i → ∃ g : A.toGrp ⟶ B.toGrp, g ≫ j = i := by
  obtain ⟨J, hJ, jn, hcj, hsurj, huniv⟩ :=
    exists_universal (AffineCoordinates.corepresentation G) hfin
  let eG := AffineCoordinates.groupSchemeIso G
  refine ⟨splitTorus.commGroupScheme _ J,
    (torusIso _ J).inv ≫ groupSchemeMap (latticeCorep _ _) (AffineCoordinates.corepresentation G)
      jn ≫ eG.hom, ⟨⟨isSplitTorus_splitTorus J, ?_⟩, ?_⟩, ?_⟩
  · exact IsClosedSubgroup.iso_comp (torusIso _ J).symm
      ((isClosedSubgroup_groupSchemeMap _ _ hsurj).comp_iso eG)
  · exact ((isCentral_groupSchemeMap _ _ hcj).comp_iso eG).comp _
  · rintro A i ⟨I, hI, ⟨eA⟩⟩ hi
    let φ := ((torusIso _ I).hom ≫ eA.inv) ≫ i ≫ eG.symm.hom
    have hφ : IsCentral φ := (hi.comp_iso eG.symm).comp _
    let α := natOfHom (latticeCorep _ (FreeAbelianGroup I)) (AffineCoordinates.corepresentation G) φ
    have hα : groupSchemeMap _ _ α = φ := groupSchemeMap_natOfHom _ _ φ
    have hαc : IsCentralNat α := isCentralNat_of_isCentral _ _ (hα ▸ hφ)
    obtain ⟨l, hl⟩ := huniv (FreeAbelianGroup I) α hαc
    refine ⟨eA.hom ≫ (torusIso _ I).inv ≫
      groupSchemeMap (latticeCorep _ _) (latticeCorep _ _) (latticeMap l) ≫ (torusIso _ J).hom, ?_⟩
    have hcomp := SplitComponent.groupSchemeMap_comp (latticeCorep _ (FreeAbelianGroup I))
      (latticeCorep _ (FreeAbelianGroup J)) (AffineCoordinates.corepresentation G) (latticeMap l) jn
    rw [hl, hα] at hcomp
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (groupSchemeMap _ _ (latticeMap l)), ← hcomp]
    simp [φ]

end Field

/-- **Existence and uniqueness of the split component** (Renard V.2.1). Over every field `k`,
a connected reductive group `G` has a split component, and any two split components are
isomorphic over `G`. -/
theorem splitComponentStatement : SplitComponentStatement.{u} := by
  intro k _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨B, j, hj, huniv⟩ := exists_largestCentralSplitTorus G (finiteType_coordinateAlgebra G)
  have hmax : IsSplitComponent j := by
    refine ⟨hj, fun A' i' hi' f hf => ?_⟩
    obtain ⟨g, hg⟩ := huniv A' i' hi'.1.1 hi'.2
    refine ⟨⟨g, ?_, ?_⟩⟩
    · apply hj.1.2.cancel
      rw [Category.assoc, hg, hf, Category.id_comp]
    · apply hi'.1.2.cancel
      rw [Category.assoc, hf, hg, Category.id_comp]
  refine ⟨⟨B, j, hmax⟩, fun A A' i i' hi hi' => ?_⟩
  obtain ⟨g, hg⟩ := huniv A i hi.1.1.1 hi.1.2
  obtain ⟨g', hg'⟩ := huniv A' i' hi'.1.1.1 hi'.1.2
  have : IsIso g := hi.2 B j hj g hg
  have : IsIso g' := hi'.2 B j hj g' hg'
  refine ⟨asIso g ≪≫ (asIso g').symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc, ← hg', IsIso.inv_hom_id_assoc,
    hg]

end Langlands.GroupScheme
