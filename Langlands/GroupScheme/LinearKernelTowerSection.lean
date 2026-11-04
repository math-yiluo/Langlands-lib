import Langlands.GroupScheme.LinearKernelTower
import Langlands.GroupScheme.LinearAdditiveExtensionSplittingStatement
import Langlands.GroupScheme.SplitSolvableExtension

/-! # Homomorphic sections of character-linear kernel towers over diagonalizable groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {S : Scheme.{u}} {H G G' : GroupScheme S}

/-- Transport an automorphic action along an isomorphism of the acted-on group schemes, keeping
the acting group. -/
def transportActed (b : AutomorphicAction H G) (e : G ≅ G') : AutomorphicAction H G' where
  hom := (H.X ◁ e.inv.hom.hom) ≫ b.hom ≫ e.hom.hom.hom
  one_left g := by
    have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ := by
      rw [← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom]
    have he' : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ := by
      rw [← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom]
    rw [lift_whiskerLeft_assoc, ← Category.assoc, b.one_left, Category.assoc, he',
      Category.comp_id]
  mul_left h h' g := by
    have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ := by
      rw [← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom]
    simp only [lift_whiskerLeft_assoc, Category.assoc, he, Category.comp_id]
    rw [← Category.assoc, b.mul_left, Category.assoc]
  mul_right h g g' := by
    simp only [lift_whiskerLeft_assoc]
    rw [MonObj.mul_comp, ← Category.assoc, b.mul_right, MonObj.mul_comp, Category.assoc,
      Category.assoc]

@[simp] theorem transportActed_act (b : AutomorphicAction H G) (e : G ≅ G') {T : Over S}
    (h : T ⟶ H.X) (x : T ⟶ G'.X) :
    (b.transportActed e).act h x = b.act h (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom := by
  simp only [act, transportActed, lift_whiskerLeft_assoc, Category.assoc]

end AutomorphicAction

namespace LinearKernelTower

variable {k : Type u} [Field k]

/-- A homomorphic section of a homomorphism out of an affine group scheme is a closed subgroup:
the underlying morphism of the homomorphism is separated, because its source is affine. -/
theorem isClosedSubgroup_of_section {Q D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom Q.X.hom] (r : Q ⟶ D) (t : D ⟶ Q) (ht : t ≫ r = 𝟙 D) :
    IsClosedSubgroup t := by
  change IsClosedImmersion t.hom.hom.left
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have he : t.hom.hom.left ≫ r.hom.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, ht, Grp.id_hom_hom, Over.id_left]
  have : IsClosedImmersion (t.hom.hom.left ≫ r.hom.hom.left) := by
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp _ r.hom.hom.left

variable [IsAlgClosed k] {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ]

/-- One step of a tower. Let `q = p ≫ r`, where `p : E ⟶ Q` is an fppf quotient by its full
kernel and this kernel is character-linear for `q`. If `r` has a homomorphic section `t`,
Milne's splitting theorem 15.34(d), applied to the inverse image of `t` in `E`, gives a
homomorphic section of `q`. -/
theorem exists_section_of_step (hsplit : LinearAdditiveExtensionSplittingStatement.{u})
    {E Q : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType E.X.hom] [IsAffineHom E.X.hom] [IsAffineHom Q.X.hom]
    (p : E ⟶ Q) (r : Q ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι p)) p)
    (hK : IsCharacterLinearKernel (Diagonalizable.groupScheme (CommRingCat.of k) Λ)
      (p ≫ r) p)
    (t : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ Q) (ht : t ≫ r = 𝟙 _) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E,
      s ≫ p ≫ r = 𝟙 _ := by
  obtain ⟨a, χ, b, ha, hconj, hlin⟩ := hK
  have htc : IsClosedSubgroup t := isClosedSubgroup_of_section r t ht
  -- The inverse image `E'` of the section, with inclusion `incl` and projection `π` onto `D`.
  let incl := SubgroupPreimage.inclusion p t
  let π := SubgroupPreimage.projection p t
  have hw : incl ≫ p = π ≫ t := subgroupIntersection_condition p t
  have hinclc : IsClosedSubgroup incl := SubgroupPreimage.isClosedSubgroup p t htc
  have : IsClosedImmersion incl.hom.hom.left := hinclc
  have : Mono incl.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom (SubgroupPreimage.groupScheme p t).X.hom :=
    SubgroupPreimage.isAffineHom p t htc
  have : LocallyOfFiniteType (SubgroupPreimage.groupScheme p t).X.hom := by
    rw [← Over.w incl.hom.hom]
    infer_instance
  -- The kernel of `π` is the kernel of `p`.
  have h0 : kernelι p ≫ p = 0 := SplitSolvable.kernel_comp_eq_zero hp
  let z := SubgroupPreimage.kernelInclusion p t (kernelι p) h0
  have : Mono z.hom.hom := SubgroupPreimage.kernelInclusion_mono p t (kernelι p) h0
  have hπ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) π :=
    SubgroupPreimage.isFppfQuotient_projection p t (kernelι p) h0 hp
  have hz : (SubgroupFunctor.range z).IsRepresentedBy z := ⟨inferInstance, rfl⟩
  let e := hπ.kernelIso hz
  have he : e.hom ≫ kernelι π = z := hπ.kernelIso_hom_comp hz
  have hzincl : z ≫ incl = kernelι p :=
    SubgroupPreimage.kernelInclusion_comp_inclusion p t (kernelι p) h0
  have hinv : e.inv ≫ z = kernelι π := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hinvincl : (kernelι π).hom.hom ≫ incl.hom.hom = e.inv.hom.hom ≫ (kernelι p).hom.hom := by
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, ← hinv, Category.assoc, hzincl]
  have hπt : incl ≫ p ≫ r = π := by
    rw [← Category.assoc, hw, Category.assoc, ht, Category.comp_id]
  -- Transport the linear data to the kernel of `π`.
  have ha' : IsClosedSubgroup (e.inv ≫ a) := by
    change IsClosedImmersion (e.inv.hom.hom.left ≫ a.hom.hom.left)
    have : IsClosedImmersion a.hom.hom.left := ha
    have : IsIso e.inv.hom.hom.left := by
      have : IsIso e.inv := inferInstance
      exact (Grp.forget _ ⋙ Over.forget _).map_isIso e.inv
    infer_instance
  obtain ⟨s', hs'⟩ := hsplit k Λ (SubgroupPreimage.groupScheme p t) π hπ.1 hπ.2.1 hπ.2.2.1
    (e.inv ≫ a) ha' χ (b.transportActed e)
    (by
      intro T g x
      apply (cancel_mono incl.hom.hom).mp
      have h1 : e.hom.hom.hom ≫ (kernelι π).hom.hom ≫ incl.hom.hom = (kernelι p).hom.hom := by
        rw [← hzincl, ← he]
        simp only [Grp.comp_hom_hom, Category.assoc]
      have hg : g ≫ π.hom.hom = (g ≫ incl.hom.hom) ≫ (p ≫ r).hom.hom := by
        rw [Category.assoc, ← Grp.comp_hom_hom, hπt]
      simp only [AutomorphicAction.transportActed_act, Category.assoc]
      rw [h1, hg, hconj, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
      simp only [Category.assoc, hinvincl])
    (by
      intro T d x
      rw [AutomorphicAction.transportActed_act, Grp.comp_hom_hom, Category.assoc,
        ← Category.assoc e.hom.hom.hom, ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom,
        Category.id_comp, hlin, Category.assoc])
  refine ⟨s' ≫ incl, ?_⟩
  rw [Category.assoc, hπt, hs']

/-- Every finite character-linear kernel tower over a diagonalizable group, over an
algebraically closed field, has a homomorphic section, given Milne's splitting theorem
15.34(d) in the form `LinearAdditiveExtensionSplittingStatement`. -/
theorem exists_section_of_hasTower (hsplit : LinearAdditiveExtensionSplittingStatement.{u}) :
    ∀ (n : ℕ) {E : GroupScheme (Spec (CommRingCat.of k))}
      (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
      HasTower (Diagonalizable.groupScheme (CommRingCat.of k) Λ) n q →
        ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E, s ≫ q = 𝟙 _
  | 0, E, q, h => by
    have : IsIso q := h.2.2
    exact ⟨inv q, IsIso.inv_hom_id q⟩
  | n + 1, E, q, h => by
    obtain ⟨hft, haff, Q, p, r, hp, hpr, hK, hr⟩ := h
    have : LocallyOfFiniteType E.X.hom := hft
    have : IsAffineHom E.X.hom := haff
    have : IsAffineHom Q.X.hom := hr.isAffineHom
    obtain ⟨t, ht⟩ := exists_section_of_hasTower hsplit n r hr
    subst hpr
    exact exists_section_of_step hsplit p r hp hK t ht

/-- A homomorphism that admits a finite character-linear kernel tower has a homomorphic
section, given `LinearAdditiveExtensionSplittingStatement`. -/
theorem exists_section_of_admitsTower (hsplit : LinearAdditiveExtensionSplittingStatement.{u})
    {E : GroupScheme (Spec (CommRingCat.of k))}
    {q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp}
    (h : AdmitsTower (Diagonalizable.groupScheme (CommRingCat.of k) Λ) q) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E, s ≫ q = 𝟙 _ := by
  obtain ⟨n, hn⟩ := h
  exact exists_section_of_hasTower hsplit n q hn

end LinearKernelTower

end Langlands.GroupScheme
