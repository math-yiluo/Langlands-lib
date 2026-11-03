import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Absolute.SolvableSubgroupBorelContainmentStatement
import Langlands.GroupScheme.Torus.Geometry

/-! # Reduction of maximal-torus conjugacy to Borel subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Scheme

variable {S : Scheme.{u}} {G : GroupScheme S} {T T' : CommGroupScheme S}

/-- For commutative sources, rational subgroup conjugacy has an isomorphism
in the category of commutative group schemes. -/
theorem subgroupConjugate_iff_exists_commGroupSchemeIso
    (j : T.toGrp ⟶ G) (j' : T'.toGrp ⟶ G) :
    SubgroupConjugate j j' ↔
      ∃ (g : Over.mk (𝟙 S) ⟶ G.X) (e : T ≅ T'),
        j ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j' := by
  constructor
  · rintro ⟨g, e, he⟩
    let e' : T ≅ T' :=
      { hom := Additive.ofMul e.hom
        inv := Additive.ofMul e.inv
        hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
        inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
    exact ⟨g, e', he⟩
  · rintro ⟨g, e, he⟩
    let e' : T.toGrp ≅ T'.toGrp :=
      { hom := CommGroupScheme.groupHom e.hom
        inv := CommGroupScheme.groupHom e.inv
        hom_inv_id := congrArg CommGroupScheme.groupHom e.hom_inv_id
        inv_hom_id := congrArg CommGroupScheme.groupHom e.inv_hom_id }
    exact ⟨g, e', he⟩

end Scheme

section Field

variable {k : Type u} [Field k]
variable {G B B' : GroupScheme (Spec (CommRingCat.of k))}
variable {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Each maximal torus of this group factors through a Borel subgroup. -/
def MaximalToriLieInBorels (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
    IsMaximalTorus j →
      ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelPair i j

/-- Conjugate closed overgroups reduce ambient maximal-torus conjugacy
to maximal-torus conjugacy in the second overgroup. -/
theorem SubgroupConjugate.of_maximalTorus_overgroups
    (i : B ⟶ G) (i' : B' ⟶ G) (f : T.toGrp ⟶ B) (f' : T'.toGrp ⟶ B')
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (hf : IsMaximalTorus (f ≫ i)) (hf' : IsMaximalTorus (f' ≫ i'))
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (e : B ≅ B')
    (he : i ≫ (G.innerIso g).hom = e.hom ≫ i')
    (hB' : MaximalToriAreConjugate B') :
    SubgroupConjugate (f ≫ i) (f' ≫ i') := by
  apply SubgroupConjugate.of_overgroups i i' f f' g e he
  exact hB' T T' (f ≫ e.hom) f'
    ((IsMaximalTorus.of_comp hi hf).comp_iso e)
    (IsMaximalTorus.of_comp hi' hf')

/-- Borel containment and the two conjugacy inputs imply conjugacy
of maximal tori in the ambient group. -/
theorem MaximalToriAreConjugate.of_borel_inputs
    (hcontain : MaximalToriLieInBorels G)
    (hBorel : ∀ (B B' : GroupScheme (Spec (CommRingCat.of k)))
      (i : B ⟶ G) (i' : B' ⟶ G),
      IsBorelSubgroup i → IsBorelSubgroup i' → SubgroupConjugate i i')
    (hinside : ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
      IsBorelSubgroup i → MaximalToriAreConjugate B) :
    MaximalToriAreConjugate G := by
  intro T T' j j' hj hj'
  obtain ⟨B, i, hi, _, f, hf⟩ := hcontain T j hj
  obtain ⟨B', i', hi', _, f', hf'⟩ := hcontain T' j' hj'
  obtain ⟨g, e, he⟩ := hBorel B B' i i' hi hi'
  have hc := SubgroupConjugate.of_maximalTorus_overgroups i i' f f'
    hi.isClosedSubgroup hi'.isClosedSubgroup (hf.symm ▸ hj) (hf'.symm ▸ hj')
    g e he (hinside B' i' hi')
  simpa only [hf, hf'] using hc

end Field

/-- The exact geometric maximal-torus conjugacy statement follows
conditionally from Borel conjugacy, containment, and solvable-group conjugacy. -/
theorem maximalTorusConjugacyStatement_of_borel_inputs
    (hBorel : BorelConjugacyStatement.{u})
    (hcontain : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (G : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
      MaximalToriLieInBorels G)
    (hsolvable : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (B : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left],
      IsSolvableGroupScheme B → MaximalToriAreConjugate B) :
    MaximalTorusConjugacyStatement.{u} := by
  intro k _ _ G _ _ _ T T' j j' hj hj'
  apply (subgroupConjugate_iff_exists_commGroupSchemeIso j j').mp
  apply MaximalToriAreConjugate.of_borel_inputs (hcontain k G) ?_ ?_ T T' j j' hj hj'
  · intro B B' i i' hi hi'
    exact (hBorel k G).2 B B' i i' hi hi'
  · intro B i hi
    let : Smooth B.X.hom := hi.smooth
    let : ConnectedSpace B.X.left := hi.connectedSpace
    let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
    let : IsAffineHom B.X.hom := by
      rw [← Over.w i.hom.hom]
      infer_instance
    exact hsolvable k B hi.isSolvableGroupScheme

/-- Containment of each given solvable subgroup places each given maximal torus in a Borel. -/
theorem maximalToriLieInBorels_of_solvableSubgroupBorelContainment
    (hcontain : SolvableSubgroupBorelContainmentStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] :
    MaximalToriLieInBorels G := by
  intro T j hj
  let : Smooth T.toGrp.X.hom := hj.1.smooth
  let : ConnectedSpace T.toGrp.X.left := hj.1.connectedSpace
  obtain ⟨B, i, f, hi, hf⟩ := hcontain k G T.toGrp j hj.2.1
    (isSolvableGroupScheme_of_isCommMonObj T.toGrp)
  exact ⟨B, i, hi, hj, f, hf⟩

/-- The general solvable containment input can be used in the existing conjugacy reduction. -/
theorem maximalTorusConjugacyStatement_of_solvableSubgroupBorelContainment
    (hBorel : BorelConjugacyStatement.{u})
    (hcontain : SolvableSubgroupBorelContainmentStatement.{u})
    (hsolvable : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (B : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left],
      IsSolvableGroupScheme B → MaximalToriAreConjugate B) :
    MaximalTorusConjugacyStatement.{u} :=
  maximalTorusConjugacyStatement_of_borel_inputs hBorel
    (maximalToriLieInBorels_of_solvableSubgroupBorelContainment hcontain) hsolvable


end Langlands.GroupScheme
