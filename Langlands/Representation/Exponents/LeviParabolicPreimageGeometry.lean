import Langlands.Representation.Exponents.LeviParabolicPreimage
import Langlands.GroupScheme.Rational.LeviPreimageSolvableRadical
import Langlands.GroupScheme.Absolute.ParabolicBorelFactorization
import Langlands.GroupScheme.Absolute.BorelIdentityComponent
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Rational.SplitUnipotentProductBaseChange
import Langlands.GroupScheme.Derived.CentralIntersectionReduction
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Parabolicity of actual inverse images under a supplied Levi retraction -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviPreimage

section Base

variable {S S' : Scheme.{u}} {P M U : GroupScheme S}
    (l : M ⟶ P) (r : U ⟶ P) [IsIso (subgroupMultiplication l r)]
    (hn : (SubgroupFunctor.range r).IsNormal)

/-- The original multiplication isomorphism is preserved by base change. -/
theorem isIso_multiplication_baseChange (b : S' ⟶ S) :
    IsIso (subgroupMultiplication ((GroupScheme.baseChange b).map l)
      ((GroupScheme.baseChange b).map r)) := by
  have he := subgroupMultiplication_baseChange b l r
  have hi : IsIso ((Over.pullback b).map (subgroupMultiplication l r)) := by
    infer_instance
  rw [← he] at hi
  let := hi
  exact IsIso.of_isIso_comp_left (subgroupMultiplicationBaseChangeIso b M U).hom _

/-- A homomorphism that fixes the supplied Levi and kills the supplied radical
is the actual Levi retraction. -/
theorem retraction_unique (t : P ⟶ M) (hlt : l ≫ t = 𝟙 M) (hrt : r ≫ t = 0) :
    t = leviRetraction l r hn := by
  apply hom_ext_points
  intro T x
  rw [comp_leviRetraction]
  conv_lhs => rw [← leviComponent_mul_radicalComponent l r x]
  rw [MonObj.mul_comp, Category.assoc, Category.assoc,
    ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hlt, hrt]
  simp only [Grp.id_hom_hom, Category.comp_id, Grp.zero_hom, Mon.zero_hom,
    ← Hom.one_def, MonObj.comp_one, mul_one]

/-- The supplied retraction commutes with arbitrary base change. -/
theorem retraction_baseChange (b : S' ⟶ S)
    (hn' : (SubgroupFunctor.range ((GroupScheme.baseChange b).map r)).IsNormal) :
    (GroupScheme.baseChange b).map (leviRetraction l r hn) =
      @leviRetraction S' _ _ _ ((GroupScheme.baseChange b).map l)
        ((GroupScheme.baseChange b).map r) (isIso_multiplication_baseChange l r b) hn' := by
  have := isIso_multiplication_baseChange l r b
  apply retraction_unique _ _ hn'
  · rw [← Functor.map_comp, levi_comp_leviRetraction]
    exact (GroupScheme.baseChange b).map_id M
  · rw [← Functor.map_comp, radical_comp_leviRetraction, Functor.map_zero]

end Base

variable {k : Type u} [Field k]
    {P M U C : GroupScheme (Spec (CommRingCat.of k))}
    (l : M ⟶ P) (r : U ⟶ P) [IsIso (subgroupMultiplication l r)]
    (hn : (SubgroupFunctor.range r).IsNormal) (c : C ⟶ M)

/-- A Borel pulls back to a Borel through a supplied smooth connected unipotent
Levi kernel. -/
theorem isBorelSubgroup_inclusion
    [IsAffineHom P.X.hom] [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
    [IsAffineHom U.X.hom] [Smooth U.X.hom] [GeometricallyConnected U.X.hom]
    (hU : IsUnipotent U) (hc : IsBorelSubgroup c) :
    IsBorelSubgroup (inclusion l r hn c) := by
  let t := leviRetraction l r hn
  have : Smooth t.hom.hom.left := smooth_leviRetraction l r hn
  have : GeometricallyConnected t.hom.hom.left :=
    geometricallyConnected_leviRetraction l r hn
  have : Smooth C.X.hom := hc.smooth
  have : ConnectedSpace C.X.left := hc.connectedSpace
  have : IsClosedImmersion c.hom.hom.left := hc.isClosedSubgroup
  have : IsAffineHom C.X.hom := by
    rw [← Over.w c.hom.hom]
    infer_instance
  refine ⟨SubgroupPreimage.isClosedSubgroup t c hc.isClosedSubgroup,
    SubgroupPreimage.smooth t c, SubgroupPreimage.connectedSpace t c, ?_, ?_⟩
  · apply isSolvableGroupScheme_of_isSolvable_points
    have : Group.IsSolvable (algebraicClosurePoint k ⟶ U.X) :=
      isSolvable_points_of_isUnipotent hU _
    have : Group.IsSolvable (algebraicClosurePoint k ⟶ C.X) :=
      SolvableFieldExtensionProof.allPoints_isSolvable C hc.smooth
        hc.isSolvableGroupScheme _
    exact isSolvable_points_leviPreimage l r hn c _
  · intro H h f hh hHs hHc hHsol hf
    have : Smooth H.X.hom := hHs
    have : ConnectedSpace H.X.left := hHc
    have : IsClosedImmersion h.hom.hom.left := hh
    have : IsAffineHom H.X.hom := by
      rw [← Over.w h.hom.hom]
      infer_instance
    obtain ⟨D, j, a, hj, haj, hflat, hsurj, hqc, hlfp, hDs, hDc, hDa⟩ :=
      HomImage.exists_image (h ≫ t)
    have : Smooth D.X.hom := hDs
    have : IsAffineHom D.X.hom := hDa
    have : Surjective a.hom.hom.left := hsurj
    have hDsol : IsSolvableGroupScheme D :=
      LeviPreimageRadical.isSolvableGroupScheme_of_surjective a hHsol
    let g : C ⟶ D := leviSection l r hn c ≫ f ≫ a
    have hgj : g ≫ j = c := by
      simp only [g, Category.assoc]
      rw [haj, ← Category.assoc f, hf, ← Category.assoc,
        section_inclusion, Category.assoc, levi_comp_leviRetraction, Category.comp_id]
    have : IsIso g := hc.maximal D j g hj hDs hDc hDsol hgj
    have hback : h ≫ t = (a ≫ inv g) ≫ c := by
      rw [← hgj]
      simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using haj.symm
    let back : H ⟶ group l r hn c := pullback.lift h (a ≫ inv g) hback
    have hbi : back ≫ inclusion l r hn c = h := pullback.lift_fst _ _ _
    have : Mono (inclusion l r hn c) := by
      have : IsClosedImmersion (inclusion l r hn c).hom.hom.left :=
        SubgroupPreimage.isClosedSubgroup t c hc.isClosedSubgroup
      have : Mono (inclusion l r hn c).hom.hom := Over.mono_of_mono_left _
      exact (Grp.forget _).mono_of_mono_map
        (inferInstance : Mono (inclusion l r hn c).hom.hom)
    have : Mono h := by
      have : Mono h.hom.hom := Over.mono_of_mono_left _
      exact (Grp.forget _).mono_of_mono_map (inferInstance : Mono h.hom.hom)
    refine ⟨⟨back, ?_, ?_⟩⟩
    · apply (cancel_mono (inclusion l r hn c)).mp
      simp only [Category.assoc, hbi, hf, Category.id_comp]
    · apply (cancel_mono h).mp
      simp only [Category.assoc, hf, hbi, Category.id_comp]

/-- The actual inverse image of an inner parabolic is an ambient parabolic. -/
theorem isParabolicSubgroup_ambient {G : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hc : IsParabolicSubgroup c) :
    IsParabolicSubgroup (inclusion l r hn c ≫ p) := by
  have : IsAffineHom P.X.hom := hl.isAffineHom
  have : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
  have : Smooth M.X.hom := hl.isConnectedReductive.smooth
  have : Smooth U.X.hom := hr.1.smooth
  have : IsClosedImmersion r.hom.hom.left := hr.1.isClosedSubgroup
  have : IsAffineHom U.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  have : Smooth C.X.hom := hc.smooth
  have : Smooth (leviRetraction l r hn).hom.hom.left := smooth_leviRetraction l r hn
  have hi : IsClosedSubgroup (inclusion l r hn c) :=
    SubgroupPreimage.isClosedSubgroup _ c hc.isClosedSubgroup
  refine ⟨hi.comp hp.isClosedSubgroup, SubgroupPreimage.smooth _ c, ?_⟩
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have hmul : IsIso (subgroupMultiplication (F.map l) (F.map r)) :=
    isIso_multiplication_baseChange l r b
  have hn' : (SubgroupFunctor.range (F.map r)).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange b
  have ht : F.map (leviRetraction l r hn) = leviRetraction (F.map l) (F.map r) hn' :=
    retraction_baseChange l r hn b hn'
  have : IsAffineHom (F.obj P).X.hom := by
    change IsAffineHom (pullback.snd P.X.hom b)
    infer_instance
  have : Smooth (F.obj P).X.hom := by
    have : Smooth P.X.hom := hp.smooth
    change Smooth (pullback.snd P.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj M).X.hom := by
    change IsAffineHom (pullback.snd M.X.hom b)
    infer_instance
  have : Smooth (F.obj M).X.hom := by
    change Smooth (pullback.snd M.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj U).X.hom := by
    change IsAffineHom (pullback.snd U.X.hom b)
    infer_instance
  have : Smooth (F.obj U).X.hom := hr.2.smooth
  have : ConnectedSpace (F.obj U).X.left := hr.2.connectedSpace
  have : GeometricallyConnected (F.obj U).X.hom :=
    geometricallyConnected_of_connected (F.obj U)
  obtain ⟨B, j, f, hj, hf⟩ := hc.exists_isBorelSubgroup
  let iB := inclusion (F.map l) (F.map r) hn' j
  have hB : IsBorelSubgroup iB :=
    isBorelSubgroup_inclusion (F.map l) (F.map r) hn' j hr.2.isUnipotent hj
  have hambient : IsBorelSubgroup (iB ≫ F.map p) := by
    apply (borelSubgroupsAreConjugate_of_borelConjugacy borelConjugacy).isBorelSubgroup_comp
      (F.map p) (hp.isClosedSubgroup.baseChange b) hB
    obtain ⟨B', j', f', hj', hf'⟩ := hp.exists_isBorelSubgroup
    exact ⟨B', f', hf' ▸ hj'⟩
  have hrange : SubgroupFunctor.range (F.map (inclusion l r hn c)) =
      (SubgroupFunctor.range (F.map c)).comap (F.map (leviRetraction l r hn)) := by
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupPreimage.range_inclusion,
      SubgroupFunctor.comap_baseChange, SubgroupFunctor.range_baseChangeHom]
  have hle : SubgroupFunctor.range iB ≤
      SubgroupFunctor.range (F.map (inclusion l r hn c)) := by
    rw [hrange, ht]
    intro T x hx
    change x ≫ (leviRetraction (F.map l) (F.map r) hn').hom.hom ∈
      (SubgroupFunctor.range (F.map c)).carrier T
    have hx' : x ∈ ((SubgroupFunctor.range j).comap
        (leviRetraction (F.map l) (F.map r) hn')).carrier T := by
      rwa [← SubgroupPreimage.range_inclusion]
    change ∃ y : T ⟶ B.X, y ≫ j.hom.hom =
      x ≫ (leviRetraction (F.map l) (F.map r) hn').hom.hom at hx'
    obtain ⟨y, hy⟩ := hx'
    exact ⟨y ≫ f.hom.hom, by
      change (y ≫ f.hom.hom) ≫ (F.map c).hom.hom =
        x ≫ (leviRetraction (F.map l) (F.map r) hn').hom.hom
      rw [Category.assoc, ← Grp.comp_hom_hom, hf]
      exact hy⟩
  have hrep : (SubgroupFunctor.range (F.map (inclusion l r hn c))).IsRepresentedBy
      (F.map (inclusion l r hn c)) :=
    ⟨IsClosedSubgroup.mono_overHom (hi.baseChange b), rfl⟩
  let g := hrep.factorHom iB hle
  have hg : g ≫ F.map (inclusion l r hn c) = iB := hrep.factorHom_comp iB hle
  refine ⟨_, iB ≫ F.map p, g, hambient, ?_⟩
  rw [Functor.map_comp, ← Category.assoc, hg]

/-- The actual ambient parabolic, with its exact containment and original-Levi
intersection, constructed from the supplied outer Levi decomposition. -/
def ambientParabolic {G : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hc : IsParabolicSubgroup c) :
    {pR : group l r hn c ⟶ G //
      IsParabolicSubgroup pR ∧
      SubgroupFunctor.range pR ≤ SubgroupFunctor.range p ∧
      SubgroupFunctor.range (c ≫ l ≫ p) =
        SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range pR} := by
  have : Mono p.hom.hom := hp.isClosedSubgroup.mono_overHom
  have : Mono l.hom.hom := hl.isClosedSubgroup.mono_overHom
  exact ⟨inclusion l r hn c ≫ p, isParabolicSubgroup_ambient l r hn c p hp hl hr hc,
    range_ambient_le l r hn c p, range_ambient_intersection l r hn c p⟩

end Langlands.GroupScheme.LeviPreimage
