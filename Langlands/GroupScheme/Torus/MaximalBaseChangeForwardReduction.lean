import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.CentralizerSmoothStatement
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeStatement
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.FieldCentralizerRepresentabilityProof

/-! # Reduction of the forward implication of Milne 17.82 to central tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section BaseChange

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {T : CommGroupScheme S} {G : GroupScheme S}

/-- Precomposition with an isomorphism of test schemes preserves and reflects commutation of
points. -/
private theorem commute_iso_comp_iff {A B : Over S} (e : A ≅ B) (p q : B ⟶ G.X) :
    Commute (e.hom ≫ p) (e.hom ≫ q) ↔ Commute p q := by
  constructor
  · intro h
    change p * q = q * p
    apply (cancel_epi e.hom).mp
    rw [MonObj.comp_mul, MonObj.comp_mul]
    exact h.eq
  · intro h
    change (e.hom ≫ p) * (e.hom ≫ q) = (e.hom ≫ q) * (e.hom ≫ p)
    rw [← MonObj.comp_mul, ← MonObj.comp_mul, h.eq]

/-- The all-test centralizer of a homomorphism from a commutative group scheme commutes with
arbitrary base change. -/
theorem torusCentralizer_baseChange (i : T.toGrp ⟶ G) :
    torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map i) = (torusCentralizer i).baseChange b := by
  ext T' x
  rw [SubgroupFunctor.mem_baseChange, mem_torusCentralizer_iff_universal]
  refine (mem_torusCentralizer_iff_universal
    (T := (CommGroupScheme.baseChange b).obj T) _).trans ?_
  let e := Dynamic.mapTensorPullbackIso b T' T.X
  have hfst : e.hom ≫ fst _ T.X ≫ baseChangePointsEquiv b G T' x =
      baseChangePointsEquiv b G _ (fst T' _ ≫ x) := by
    rw [baseChangePointsEquiv_naturality, Dynamic.mapTensorPullbackIso_hom_fst_assoc]
  have hsnd : e.hom ≫ snd _ T.X ≫ i.hom.hom =
      baseChangePointsEquiv b G _ (snd T' _ ≫ ((GroupScheme.baseChange b).map i).hom.hom) := by
    rw [baseChangePointsEquiv_comp, ← Category.assoc]
    congr 1
    apply Over.OverMorphism.ext
    rw [Dynamic.mapTensorPullbackIso_hom_snd_left, baseChangePointsEquiv_left]
    rfl
  rw [← commute_iso_comp_iff e, hfst, hsnd]
  exact (commute_map_iff (baseChangePointsEquiv b G _).injective).symm

end BaseChange

/-- The forward implication of Milne, Theorem 17.82: if a closed torus `i : T ⟶ G` of a smooth
affine group scheme over `k` is maximal, then its pullback `T_K ⟶ G_K` is maximal for every
field extension `K` of `k`. -/
def MaximalTorusBaseChangeForwardStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
    IsMaximalTorus i →
      IsMaximalTorus
        (T := (CommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)

/-- Smoothness of torus centralizers and the central case of Milne, Theorem 17.82, imply the
forward implication of Milne, Theorem 17.82, at every universe. -/
def MaximalTorusBaseChangeForwardReductionStatement : Prop :=
  TorusCentralizerSmoothStatement.{u} → CentralMaximalTorusBaseChangeStatement.{u} →
    MaximalTorusBaseChangeForwardStatement.{u}

/-- Reduce the forward implication to the torus centralizer, in which the torus is central.
Both structural statements remain explicit hypotheses. -/
theorem maximalTorusBaseChangeForwardReduction :
    MaximalTorusBaseChangeForwardReductionStatement.{u} := by
  intro hsmooth hcentral k K _ _ _ G _ _ T i hi
  have hT : IsTorus T.toGrp := hi.1
  have hiC : IsClosedSubgroup i := hi.2.1
  have : IsAffineHom T.toGrp.X.hom := hiC.isAffineHom
  obtain ⟨C, c, hc, hcC⟩ := fieldCentralizerRepresentability k T G this i
  have : Smooth C.X.hom := hsmooth k G T i hT hiC C c hc hcC
  have : IsAffineHom C.X.hom := hcC.isAffineHom
  have hmaxCK := hcentral k K C T (torusCentralizerFactor i hc)
    (isCentral_torusCentralizerFactor i hc) (hi.isMaximalTorus_torusCentralizerFactor hc hcC)
  set b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  refine ⟨hT.baseChange, hiC.baseChange b, ?_⟩
  intro T' i' f hT' hi' hf
  have hcK := hc.baseChange b
  rw [← torusCentralizer_baseChange] at hcK
  have hle : SubgroupFunctor.range i' ≤
      torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map i) := by
    rw [← hf]
    intro U g hg V a t
    have h := range_le_torusCentralizer i' U hg V a (t ≫ f.hom.hom)
    simpa only [Grp.comp_hom_hom, Category.assoc] using h
  let i'C := hcK.factorHom i' hle
  have h1 : i'C ≫ (GroupScheme.baseChange b).map c = i' := hcK.factorHom_comp i' hle
  apply hmaxCK.2.2 T' i'C f hT'
    (IsClosedSubgroup.of_comp (hcC.baseChange b) (by rw [h1]; exact hi'))
  apply hcK.hom_ext
  rw [Category.assoc, h1, hf]
  exact (congrArg (GroupScheme.baseChange b).map (torusCentralizerFactor_comp i hc)).symm.trans
    ((GroupScheme.baseChange b).map_comp _ c)

end Langlands.GroupScheme
