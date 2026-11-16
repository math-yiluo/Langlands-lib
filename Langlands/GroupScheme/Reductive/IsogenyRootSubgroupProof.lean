import Langlands.GroupScheme.Reductive.IsogenyRootSubgroupStatement
import Langlands.GroupScheme.Rational.VectorLinePrescribedMonomial
import Langlands.GroupScheme.Reductive.IsogenyRootRestriction

/-! # Actual root-subgroup images and prescribed characteristic-power coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    {J J' : Type u} [Finite J] [Finite J']
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
    [P.IsReduced] [P'.IsReduced]

local notation "V" => VectorGroup.groupScheme (CommRingCat.of k) 1

/-- The supplied root factor computes an actual epimorphic root restriction in
arbitrary supplied equivariant additive parametrizations, on every test scheme. -/
theorem scalarPoint_comp_of_rootDatumIsogeny
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}
    (hT : IsSplitTorus T.toGrp)
    (φ : G ⟶ G') (t : T ⟶ T')
    (hsq : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny (ringExpChar k) P' P)
    (hweight : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ)
    (j' : J') (x : V ⟶ G) (x' : V ⟶ G')
    (hx' : (subgroup i' (P'.root j')).IsRepresentedBy x')
    (heq : VectorGroup.IsTorusEquivariant i x (P.root (f.indexEquiv j')))
    (heq' : VectorGroup.IsTorusEquivariant i' x' (P'.root j'))
    (p : V ⟶ V) [Epi p.hom.hom] (hp : p ≫ x' = x ≫ φ) :
    ∃ c : kˣ, ∀ (Z : Over (Spec (CommRingCat.of k))) (a : Γ(Z.left, ⊤)),
      VectorGroup.scalarPoint (CommRingCat.of k) Z a ≫ x.hom.hom ≫ φ.hom.hom =
        VectorGroup.scalarPoint (CommRingCat.of k) Z
          (Z.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (c : k)) *
            a ^ f.rootFactor j') ≫ x'.hom.hom := by
  let : Mono x'.hom.hom := hx'.1
  have hβ : t ≫ P'.root j' = f.rootFactor j' • P.root (f.indexEquiv j') := by
    rw [← hweight, f.root_weightMap, natCast_zsmul]
  exact heq.exists_scalarPoint_comp_of_restriction heq' hT (P.ne_zero _)
    φ t hsq p hp (f.rootFactor j') hβ

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.GroupScheme

/-- Actual root-subgroup fppf images and prescribed characteristic-power
coordinates of any compatible split reductive isogeny. -/
theorem isogenyRootSubgroup : IsogenyRootSubgroupStatement.{u} := by
  classical
  intro k _ G G' hG hG' T T' hT hT'
  let := hT.finite_characterLattice
  let := hT.finite_cocharacterLattice
  let := hT'.finite_characterLattice
  let := hT'.finite_cocharacterLattice
  intro i i' hi hi' φ t hφ hsquare J J' _ _ P P' _ _ hP hP'
  let := hG.isAffineHom
  let := hG'.isAffineHom
  let := hG.smooth
  let := hG'.smooth
  let := hφ.1
  intro f hweight _hco j'
  constructor
  · intro j
    exact RelativeRoot.isFppfImage_iff_index_eq P P' hT hT' i i' hP'
      φ t hsquare f hweight j' hG hG' hi hi' hP j
  · intro x x' hx hx' heq heq'
    let q := RelativeRoot.rootRestrictionOfRootDatumIsogeny P P' hT hT' i i' hP'
      φ t hsquare f hweight j' hx hx'
    have hq : IsIsogeny q :=
      RelativeRoot.isIsogeny_rootRestrictionOfRootDatumIsogeny P P' hT hT' i i' hP'
        φ t hsquare f hweight j' hG hG' hi hi' hP hx hx'
    let : Flat q.hom.hom.left := hq.2.1
    let : Surjective q.hom.hom.left := hq.2.2
    let : Epi q.hom.hom.left := Flat.epi_of_flat_of_surjective _
    let : Epi q.hom.hom := Over.epi_of_epi_left _
    exact RelativeRoot.scalarPoint_comp_of_rootDatumIsogeny P P' hT φ t hsquare f
      hweight j' x x' hx' heq heq' q
      (RelativeRoot.rootRestrictionOfRootDatumIsogeny_comp P P' hT hT' i i' hP'
        φ t hsquare f hweight j' hx hx')

end Langlands.GroupScheme
