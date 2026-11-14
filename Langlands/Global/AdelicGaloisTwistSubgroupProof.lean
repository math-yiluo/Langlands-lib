import Langlands.Global.AdelicGaloisTwistSubgroup
import Langlands.Global.AdelicGaloisTwistNormOneProof
import Langlands.Global.AdelicNormalizerConjugation
import Langlands.Global.AdelicGaloisBorelTwistingProof
import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Lemma S: Galois twisting of norm-one points of `G_L` and of its closed subgroups

Proofs of `GaloisTwistNormOneStatement` (S1) and `GaloisTwistSubgroupStatement` (S2).
Both follow from the descent equation `twistPoint_comp_radicalGaloisHom` (D1) and Lemma C
(`twistPoint_mem_normOneSubgroup`). Equalities between the two syntactic forms of `G_L`
(`AffineWeil.unitBaseChange F L G` and `(GroupScheme.baseChange (algebraBaseMap F L)).obj G`)
are used only in small lemmas about abstract points, which keeps kernel checking fast.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Postcomposition with a group-scheme homomorphism preserves norm-one adelic points,
stated for points of the adelic test object. The homomorphism is a variable, so the kernel
never unfolds a concrete instance of it. -/
theorem comp_mem_normOneSubgroup {L : Type u} [Field L] [NumberField L]
    {H K : GroupScheme (Spec (CommRingCat.of L))} (φ : H ⟶ K) (y : adeleTest L ⟶ H.X)
    (hy : (y : AdelicGroupPoints L H) ∈ normOneSubgroup L H) :
    ((y ≫ φ.hom.hom : adeleTest L ⟶ K.X) : AdelicGroupPoints L K) ∈ normOneSubgroup L K :=
  map_normOneSubgroup_le L H K φ ⟨y, hy, rfl⟩

/-- Transport of norm-one membership along an equation `y ≫ φ = z`, stated with the
equation in the syntactic form produced by `twistPoint_comp_radicalGaloisHom`. -/
theorem mem_normOneSubgroup_of_comp_eq {L : Type u} [Field L] [NumberField L]
    {H K : GroupScheme (Spec (CommRingCat.of L))} (φ : H ⟶ K) (y : adeleTest L ⟶ H.X)
    (z : AdelicGroupPoints L K)
    (hy : (y : AdelicGroupPoints L H) ∈ normOneSubgroup L H) (h : y ≫ φ.hom.hom = z) :
    z ∈ normOneSubgroup L K := by
  subst h
  exact comp_mem_normOneSubgroup φ y hy

section NormOne

variable {F L : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (σ : L ≃ₐ[F] L)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Lemma C (`twistPoint_mem_normOneSubgroup`) for `G_L` in its `unitBaseChange` form. -/
theorem twistPoint_mem_normOne_unitBaseChange
    (x : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G))
    (hx : x ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G)) :
    (twistPoint F L σ (AffineWeil.unitBaseChange F L G) x :
        AdelicGroupPoints L ((GroupScheme.baseChange (galoisBaseMap F L σ)).obj
          (AffineWeil.unitBaseChange F L G))) ∈
      normOneSubgroup L ((GroupScheme.baseChange (galoisBaseMap F L σ)).obj
          (AffineWeil.unitBaseChange F L G)) :=
  twistPoint_mem_normOneSubgroup F L σ (AffineWeil.unitBaseChange F L G) x hx

omit [NumberField F] [FiniteDimensional F L] [IsGalois F L] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] in
/-- Change of the syntactic form of `G_L` in a norm-one membership, for an abstract point. -/
theorem mem_normOneSubgroup_unitBaseChange
    (y : AdelicGroupPoints L ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (hy : y ∈ normOneSubgroup L ((GroupScheme.baseChange (algebraBaseMap F L)).obj G)) :
    (y : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) ∈
      normOneSubgroup L (AffineWeil.unitBaseChange F L G) :=
  hy

omit [IsGalois F L] in
/-- Descent equation D1 for the identity subgroup `j = 𝟙`. -/
theorem twistPoint_comp_radicalGaloisHom_id
    (x : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) :
    twistPoint F L σ (AffineWeil.unitBaseChange F L G) x ≫
        (radicalGaloisHom (𝟙 (AffineWeil.unitBaseChange F L G)) σ).hom.hom =
      galoisTwist F L G σ x := by
  have h := twistPoint_comp_radicalGaloisHom F L G σ (𝟙 (AffineWeil.unitBaseChange F L G)) x
  rwa [Grp.id_hom_hom, Category.comp_id] at h

/-- Lemma S1 for a fixed `σ` and point `x`. -/
theorem galoisTwist_mem_normOneSubgroup (x : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G))
    (hx : x ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G)) :
    galoisTwist F L G σ x ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G) :=
  mem_normOneSubgroup_unitBaseChange _
    (mem_normOneSubgroup_of_comp_eq (radicalGaloisHom (𝟙 (AffineWeil.unitBaseChange F L G)) σ)
      _ _ (twistPoint_mem_normOne_unitBaseChange σ x hx) (twistPoint_comp_radicalGaloisHom_id σ x))

end NormOne

/-- Lemma S1: the Galois twist of a norm-one upper adelic point is norm-one. -/
theorem galoisTwistNormOne : GaloisTwistNormOneStatement.{u} :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ σ x hx => galoisTwist_mem_normOneSubgroup σ x hx

section GenericConj

variable {L : Type u} [Field L] [NumberField L]
  {K P Q : GroupScheme (Spec (CommRingCat.of L))}

/-- If `e : P ≅ Q` identifies `φ : P → K` with `g` followed by the inner automorphism of a
base point `n`, then `y ≫ φ` is the `n`-conjugate of the image of `y ≫ e` under `g`, for
every adelic point `y` of `P`. The equation `h` has the syntactic form produced by
`twistPoint_comp_radicalGaloisHom`. -/
theorem eq_rational_conj_of_comp_eq (n : Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶ K.X)
    {φ : P ⟶ K} {g : Q ⟶ K} (e : P ≅ Q) (he : e.hom ≫ g ≫ (K.innerIso n).hom = φ)
    (y : adeleTest L ⟶ P.X) (z : AdelicGroupPoints L K) (h : y ≫ φ.hom.hom = z) :
    z = rational L K (basePointEquiv n) *
        map L Q K g ((y ≫ e.hom.hom.hom : adeleTest L ⟶ Q.X) : AdelicGroupPoints L Q) *
          (rational L K (basePointEquiv n))⁻¹ := by
  subst h he
  rw [rational_basePointEquiv, map_apply, affinePointsTarget_apply, ← K.comp_innerIso_hom n,
    Grp.comp_hom_hom, Grp.comp_hom_hom]
  simp only [Category.assoc]

end GenericConj

section Subgroup

variable {F L : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (σ : L ≃ₐ[F] L)

omit [NumberField F] [NumberField L] [FiniteDimensional F L] [IsGalois F L] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] in
/-- Closedness of the canonical Galois translate of a closed subgroup of `G_L`. -/
theorem isClosedSubgroup_radicalGaloisHom {P : GroupScheme (Spec (CommRingCat.of L))}
    (f : P ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G) (hf : IsClosedSubgroup f) :
    IsClosedSubgroup (radicalGaloisHom f σ) :=
  (hf.baseChange (galoisBaseMap F L σ)).comp_iso _

/-- The source isomorphism `P^σ ≅ Q` identifying the canonical Galois translate of `f` with
the `n`-conjugate of `g`. -/
def twistSourceIso {P Q : GroupScheme (Spec (CommRingCat.of L))}
    (f : P ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (g : Q ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap F L)).obj G).X)
    (hf : IsClosedSubgroup f) (hg : IsClosedSubgroup g)
    (hR : SubgroupFunctor.range (radicalGaloisHom f σ) =
        SubgroupFunctor.range
          (g ≫ (((GroupScheme.baseChange (algebraBaseMap F L)).obj G).innerIso n).hom)) :
    (GroupScheme.baseChange (galoisBaseMap F L σ)).obj P ≅ Q :=
  (isClosedSubgroup_radicalGaloisHom σ f hf).sourceIsoOfRangeEq (hg.comp_iso _) hR

omit [NumberField F] [NumberField L] [FiniteDimensional F L] [IsGalois F L] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] in
/-- `twistSourceIso` followed by `g` and the inner automorphism of `n` is the canonical
Galois translate of `f`. -/
theorem twistSourceIso_hom_comp {P Q : GroupScheme (Spec (CommRingCat.of L))}
    (f : P ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (g : Q ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap F L)).obj G).X)
    (hf : IsClosedSubgroup f) (hg : IsClosedSubgroup g)
    (hR : SubgroupFunctor.range (radicalGaloisHom f σ) =
        SubgroupFunctor.range
          (g ≫ (((GroupScheme.baseChange (algebraBaseMap F L)).obj G).innerIso n).hom)) :
    (twistSourceIso σ f g n hf hg hR).hom ≫ g ≫
        (((GroupScheme.baseChange (algebraBaseMap F L)).obj G).innerIso n).hom =
      radicalGaloisHom f σ :=
  IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp _ _ hR

omit [IsGalois F L] in
/-- Lemma S2 in the descent form of `G_L`: the twist of `p ≫ f` is the `n`-conjugate of
the image under `g` of the twisted point carried to `Q`. -/
theorem galoisTwist_comp_eq_conj {P Q : GroupScheme (Spec (CommRingCat.of L))}
    (f : P ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (g : Q ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap F L)).obj G).X)
    (hf : IsClosedSubgroup f) (hg : IsClosedSubgroup g)
    (hR : SubgroupFunctor.range (radicalGaloisHom f σ) =
        SubgroupFunctor.range
          (g ≫ (((GroupScheme.baseChange (algebraBaseMap F L)).obj G).innerIso n).hom))
    (p : adeleTest L ⟶ P.X) :
    galoisTwist F L G σ (p ≫ f.hom.hom) =
      rational L ((GroupScheme.baseChange (algebraBaseMap F L)).obj G) (basePointEquiv n) *
        map L Q ((GroupScheme.baseChange (algebraBaseMap F L)).obj G) g
          ((twistPoint F L σ P p ≫ (twistSourceIso σ f g n hf hg hR).hom.hom.hom :
            adeleTest L ⟶ Q.X) : AdelicGroupPoints L Q) *
          (rational L ((GroupScheme.baseChange (algebraBaseMap F L)).obj G)
            (basePointEquiv n))⁻¹ :=
  eq_rational_conj_of_comp_eq n _ (twistSourceIso_hom_comp σ f g n hf hg hR) _ _
    (twistPoint_comp_radicalGaloisHom F L G σ f p)

omit [IsGalois F L] in
/-- Passage from the descent form of `G_L` to its `unitBaseChange` form in Lemma S2, for
abstract morphisms and points. -/
theorem galoisTwist_map_eq_rationalSection_conj {P Q : GroupScheme (Spec (CommRingCat.of L))}
    (f : P ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (g : Q ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap F L)).obj G).X)
    (p : adeleTest L ⟶ P.X) (w : AdelicGroupPoints L Q)
    (h : galoisTwist F L G σ (p ≫ f.hom.hom) =
      rational L ((GroupScheme.baseChange (algebraBaseMap F L)).obj G) (basePointEquiv n) *
        map L Q ((GroupScheme.baseChange (algebraBaseMap F L)).obj G) g w *
          (rational L ((GroupScheme.baseChange (algebraBaseMap F L)).obj G)
            (basePointEquiv n))⁻¹) :
    galoisTwist F L G σ (map L P (AffineWeil.unitBaseChange F L G) f p) =
      rationalSection F L G n * map L Q (AffineWeil.unitBaseChange F L G) g w *
        (rationalSection F L G n)⁻¹ := by
  rw [rationalSection_eq_rational_basePointEquiv]
  exact h

/-- Lemma S2 for fixed data. -/
theorem exists_galoisTwist_map_eq_conj {P Q : GroupScheme (Spec (CommRingCat.of L))}
    (f : P ⟶ AffineWeil.unitBaseChange F L G) (g : Q ⟶ AffineWeil.unitBaseChange F L G)
    (m : rationalPoints (AffineWeil.unitBaseChange F L G))
    (hf : IsClosedSubgroup f) (hg : IsClosedSubgroup g)
    (hR : SubgroupFunctor.range (radicalGaloisHom f σ) =
        SubgroupFunctor.range (g ≫ ((AffineWeil.unitBaseChange F L G).innerIso m).hom))
    (p : normOneSubgroup L P) :
    ∃ q : normOneSubgroup L Q,
      galoisTwist F L G σ (map L P (AffineWeil.unitBaseChange F L G) f p) =
        rationalSection F L G m * map L Q (AffineWeil.unitBaseChange F L G) g q *
          (rationalSection F L G m)⁻¹ :=
  ⟨⟨twistPoint F L σ P p.1 ≫ (twistSourceIso σ f g m hf hg hR).hom.hom.hom,
    comp_mem_normOneSubgroup _ _ (twistPoint_mem_normOneSubgroup F L σ P p.1 p.2)⟩,
    galoisTwist_map_eq_rationalSection_conj σ f g m p.1 _
      (galoisTwist_comp_eq_conj σ f g m hf hg hR p.1)⟩

end Subgroup

/-- Lemma S2: Galois twists of norm-one points of a closed subgroup are rational conjugates
of norm-one points of any closed subgroup whose conjugate has the same range as the
canonical Galois translate. -/
theorem galoisTwistSubgroup : GaloisTwistSubgroupStatement.{u} :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ σ _ _ f g m hf hg hR p =>
    exists_galoisTwist_map_eq_conj σ f g m hf hg hR p

end Langlands.Global.AdelicGaloisUnit
