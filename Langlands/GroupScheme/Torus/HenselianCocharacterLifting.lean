import Langlands.GroupScheme.Torus.StrictHenselianMaximal
import Langlands.GroupScheme.Torus.ExponentCocharacters
import Langlands.GroupScheme.Reductive.LocalRootGroupFibre

/-! # Lifting a cocharacter of a closed split torus from the closed fibre over a Henselian ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- **Lifting a cocharacter of a closed split torus.** Let `R` be a Henselian local ring and
`G` a smooth affine group over `Spec R`. For a closed split torus `a : A ⟶ G₀` of the fibre `G₀`
of `G` at the closed point and a cocharacter `ν` of `A`, there is a cocharacter `χ` of `G` whose
base change to the closed point is `ν` followed by `a`, up to an automorphism of `G₀`. -/
theorem exists_cocharacter_baseChange_eq_comp_iso (R : Type u) [CommRing R]
    [HenselianLocalRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {A : CommGroupScheme (Spec ((Spec (CommRingCat.of R)).residueField
      (IsLocalRing.closedPoint R)))}
    (a : A.toGrp ⟶ (baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R))).obj G)
    (hA : IsSplitTorus A.toGrp) (ha : IsClosedSubgroup a) (ν : cocharacterLattice A) :
    ∃ (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G)
      (B : (baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField
          (IsLocalRing.closedPoint R))).obj G ≅
        (baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField
          (IsLocalRing.closedPoint R))).obj G),
      Dynamic.baseChangeCocharacter ((Spec (CommRingCat.of R)).fromSpecResidueField
          (IsLocalRing.closedPoint R)) χ =
        CommGroupScheme.groupHom ν ≫ a ≫ B.hom := by
  classical
  let f₀ := (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R)
  obtain ⟨U, p, hp, b, hb, T, hT, i, -, e, he⟩ :=
    relativeSplitTorusLifting (Spec (CommRingCat.of R)) G (IsLocalRing.closedPoint R)
      A.toGrp hA a ha
  obtain ⟨σ, hσ, hσb⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.henselianEtaleSection R U p hp b hb
  subst hσb
  obtain ⟨I, hI, ⟨e'⟩⟩ := hT.baseChange σ
  let := Fintype.ofFinite I
  let ic : splitTorus (Spec (CommRingCat.of R)) I ⟶ G :=
    e'.inv ≫ (baseChange σ).map i ≫ (sectionPullbackIso p σ hσ G).hom
  have he' : (baseChange (f₀ ≫ σ)).map i = e.hom ≫ a ≫
      (eqToIso (congrArg (fun f => (baseChange f).obj G) hb)).inv ≫
        (baseChangeCompIso p (f₀ ≫ σ) G).hom := by
    rw [← reassoc_of% he]
    simp
    rfl
  obtain ⟨A', B', hAB⟩ := baseChange_map_sectionPullback p σ hσ f₀ i
  let Aiso : (baseChange f₀).obj (splitTorus (Spec (CommRingCat.of R)) I) ≅ A.toGrp :=
    (baseChange f₀).mapIso e'.symm ≪≫ A' ≪≫ e
  let Biso : (baseChange f₀).obj G ≅ (baseChange f₀).obj G :=
    (eqToIso (congrArg (fun f => (baseChange f).obj G) hb)).symm ≪≫
      baseChangeCompIso p (f₀ ≫ σ) G ≪≫ B'
  have hic : (baseChange f₀).map ic = Aiso.hom ≫ a ≫ Biso.hom := by
    change (baseChange f₀).map (e'.inv ≫ ((baseChange σ).map i ≫
      (sectionPullbackIso p σ hσ G).hom)) = _
    rw [Functor.map_comp, hAB, he']
    simp [Aiso, Biso]
  let τ : (Gm (Spec ((Spec (CommRingCat.of R)).residueField
      (IsLocalRing.closedPoint R)))).toGrp ⟶
      splitTorus (Spec ((Spec (CommRingCat.of R)).residueField
        (IsLocalRing.closedPoint R))) I :=
    CommGroupScheme.groupHom ν ≫ Aiso.inv ≫ (splitTorus.baseChangeIso f₀ I).hom
  let m := splitTorus.cocharacterLatticeEquiv
    ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) I
    (Additive.ofMul τ)
  have hm : CommGroupScheme.groupHom (splitTorus.exponentCocharacter
      (Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) I m) = τ := by
    have h1 := splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm I
      (↑((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) m
    have h2 : (splitTorus.cocharacterLatticeEquiv
        (↑((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) I).symm m =
          Additive.ofMul τ :=
      AddEquiv.symm_apply_apply _ _
    exact congrArg CommGroupScheme.groupHom (h1.trans h2)
  refine ⟨CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I m) ≫ ic, Biso, ?_⟩
  rw [LocalRootGroup.baseChangeCocharacter_groupHom_comp, hm, hic]
  simp [τ]

end Langlands.GroupScheme
