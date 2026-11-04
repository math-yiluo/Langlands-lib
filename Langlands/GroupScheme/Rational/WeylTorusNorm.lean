import Langlands.GroupScheme.Rational.WeylPositiveCocharacter
import Langlands.GroupScheme.Rational.CocharacterCentralizers

/-! # The integral norm of the actual relative Weyl action on a torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

section Split

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}

/-- Centrality of every actual cocharacter implies centrality of a map from
a split torus. -/
theorem isCentral_of_forall_cocharacter (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G)
    (hi : ∀ ν : cocharacterLattice T, IsCentral (CommGroupScheme.groupHom ν ≫ i)) :
    IsCentral i := by
  obtain ⟨I, _, π, s, hsum⟩ := hT.exists_sum_comp_eq_id
  intro U x
  have hx : x = ∏ j, x ≫ (CommGroupScheme.groupHom (π j ≫ s j)).hom.hom := by
    rw [← comp_groupHom_sum, hsum]
    exact (Category.comp_id x).symm
  have hxcent : x ∈ ((center G).comap i).carrier U := by
    rw [hx]
    apply Subgroup.prod_mem
    intro j _
    change (x ≫ (CommGroupScheme.groupHom (π j ≫ s j)).hom.hom) ≫ i.hom.hom ∈
      (center G).carrier U
    rw [comp_groupHom_comp, Category.assoc, ← Grp.comp_hom_hom]
    exact hi (s j) U (x ≫ (CommGroupScheme.groupHom (π j)).hom.hom)
  exact hxcent

end Split

section Action

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- Actual normalizing rational points act by automorphisms of the source. -/
def normalizerTorusAction : normalizerPoints i →* Aut T where
  toFun n := normalizingAut i n
  map_one' :=
    (isNormalizingPoint_normalizingAut i 1).unique i IsNormalizingPoint.one
  map_mul' n m :=
    (isNormalizingPoint_normalizingAut i (n * m)).unique i
      ((isNormalizingPoint_normalizingAut i n).mul (isNormalizingPoint_normalizingAut i m))

/-- Centralizing rational points act trivially on the actual source torus. -/
theorem normalizerTorusAction_eq_one_of_mem_centralizerPoints
    {n : normalizerPoints i}
    (hn : (n : rationalPoints G) ∈ centralizerPoints i) :
    normalizerTorusAction i n = 1 :=
  (isNormalizingPoint_normalizingAut i n).unique i hn

/-- The actual quotient `N(k)/Z(k)` acts on the source torus itself. -/
def relativeWeylTorusAction : relativeWeylGroup i →* Aut T :=
  QuotientGroup.lift _ (normalizerTorusAction i) fun _ hn =>
    normalizerTorusAction_eq_one_of_mem_centralizerPoints i hn

@[simp] theorem relativeWeylTorusAction_mk (n : normalizerPoints i) :
    relativeWeylTorusAction i (QuotientGroup.mk n) = normalizingAut i n := rfl

/-- Postcomposition by the actual torus action is the published cocharacter
action of the same Weyl class. -/
theorem comp_relativeWeylTorusAction (w : relativeWeylGroup i)
    (ν : cocharacterLattice T) :
    ν ≫ (relativeWeylTorusAction i w).hom = relativeWeylCocharacterAction i w ν := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  rfl

omit [Mono i.hom.hom.left] in
/-- The ambient value of a translated torus point is actual conjugation. -/
theorem comp_normalizingAut_hom {U : Over (Spec (CommRingCat.of k))}
    (x : U ⟶ T.X) (n : normalizerPoints i) :
    (x ≫ (CommGroupScheme.groupHom (normalizingAut i n).hom).hom.hom) ≫ i.hom.hom =
      G.constantPoint (n : rationalPoints G) U * (x ≫ i.hom.hom) *
        (G.constantPoint (n : rationalPoints G) U)⁻¹ := by
  rw [Category.assoc, ← Grp.comp_hom_hom, ← isNormalizingPoint_normalizingAut,
    Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]

/-- Each Weyl translate preserves membership in any normal subgroup functor. -/
theorem relativeWeylTorusAction_eval_mem {F : SubgroupFunctor G} (hF : F.IsNormal)
    {U : Over (Spec (CommRingCat.of k))} (x : U ⟶ T.X)
    (hx : x ≫ i.hom.hom ∈ F.carrier U) (w : relativeWeylGroup i) :
    (x ≫ (CommGroupScheme.groupHom (relativeWeylTorusAction i w).hom).hom.hom) ≫
      i.hom.hom ∈ F.carrier U := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  rw [relativeWeylTorusAction_mk, comp_normalizingAut_hom]
  exact hF U _ _ (Subgroup.mem_top _) hx

end Action

section Norm

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]

/-- The sum, in the actual commutative-group-scheme Hom group, of all Weyl
automorphisms. On points this is the product of the Weyl translates. -/
def relativeWeylTorusNorm : T ⟶ T :=
  ∑ w : relativeWeylGroup i, (relativeWeylTorusAction i w).hom

/-- The norm induces precisely the published integral sum on cocharacters. -/
theorem comp_relativeWeylTorusNorm (ν : cocharacterLattice T) :
    ν ≫ relativeWeylTorusNorm i = relativeWeylCocharacterSum i ν := by
  rw [relativeWeylTorusNorm, Preadditive.comp_sum, relativeWeylCocharacterSum_apply]
  exact Finset.sum_congr rfl fun w _ => comp_relativeWeylTorusAction i w ν

/-- On every test scheme the norm preserves actual normal-subgroup membership. -/
theorem relativeWeylTorusNorm_eval_mem {F : SubgroupFunctor G} (hF : F.IsNormal)
    {U : Over (Spec (CommRingCat.of k))} (x : U ⟶ T.X)
    (hx : x ≫ i.hom.hom ∈ F.carrier U) :
    (x ≫ (CommGroupScheme.groupHom (relativeWeylTorusNorm i)).hom.hom) ≫ i.hom.hom ∈
      F.carrier U := by
  have hn : x ≫ (CommGroupScheme.groupHom (relativeWeylTorusNorm i)).hom.hom ∈
      (F.comap i).carrier U := by
    rw [relativeWeylTorusNorm, comp_groupHom_sum]
    exact Subgroup.prod_mem _ fun w _ => relativeWeylTorusAction_eval_mem i hF x hx w
  exact hn

variable [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- Actual root reflections imply that the norm has central image on every
test scheme. Reflection existence is retained as an explicit premise. -/
theorem relativeWeylTorusNorm_isCentral (hT : IsSplitTorus T.toGrp)
    (href : ∀ α ∈ relativeRoots i, ∃ w, IsRelativeReflection i α w) :
    IsCentral (CommGroupScheme.groupHom (relativeWeylTorusNorm i) ≫ i) := by
  apply isCentral_of_forall_cocharacter hT
  intro ν
  have hc := relativeWeylCocharacterSum_mem_centralCocharacters i hT href ν
  rw [mem_centralCocharacters, ← comp_relativeWeylTorusNorm] at hc
  exact hc

end Norm

end Langlands.GroupScheme
