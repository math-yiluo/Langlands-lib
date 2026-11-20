import Langlands.GroupScheme.Trigonalizable.RelativeCorrection
import Langlands.GroupScheme.Trigonalizable.PerfectOneStep

/-! # One-step splitting and tower sections compatible with a partial section -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TrigonalizableExtensionSplit

open LinearAdditiveExtension LinearKernelTower

variable {k : Type u} [Field k] {Λ Λ₁ : Type u} [AddCommGroup Λ] [AddCommGroup Λ₁]

/-- The two conditions on a weight `χ ∘ ι₁` under which the correction can be chosen compatibly
with a partial section over `ι₁` (see `exists_corrected_relative`), for a closed subgroup
`a` of `𝔾ₐ` with closed polynomial `f` of degree `N`: if `f ≠ 0`, then `χ^N ∘ ι₁ = 1` forces
`χ ∘ ι₁ = 1`, and `χ ∘ ι₁ = 1` forces `f` to be surjective on `k` or `χ^N = 1`. -/
def RelativeSolvable
    (ι₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶
      (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    {K : GroupScheme (Spec (CommRingCat.of k))}
    (a : K ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ)) : Prop :=
  (ClosedAdditivePolynomial.closedPolynomial a ≠ 0 →
    (∀ (T : Over (Spec (CommRingCat.of k)))
      (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
      VectorGroup.charValue χ T (z ≫ ι₁.hom.hom) ^
        (ClosedAdditivePolynomial.closedPolynomial a).natDegree = 1) →
    ∀ (T : Over (Spec (CommRingCat.of k)))
      (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
      VectorGroup.charValue χ T (z ≫ ι₁.hom.hom) = 1) ∧
  (ClosedAdditivePolynomial.closedPolynomial a ≠ 0 →
    (∀ (T : Over (Spec (CommRingCat.of k)))
      (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X),
      VectorGroup.charValue χ T (z ≫ ι₁.hom.hom) = 1) →
    (∀ m : k, ∃ r : k, (ClosedAdditivePolynomial.closedPolynomial a).eval r = m) ∨
      ∀ (T : Over (Spec (CommRingCat.of k)))
        (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X),
        VectorGroup.charValue χ T d ^ (ClosedAdditivePolynomial.closedPolynomial a).natDegree = 1)

/-- **One step compatible with a partial section.** Under `RelativeSolvable`, a homomorphic
section `σ₁` of `q` over `ι₁ : D(Λ₁) ⟶ D(Λ)` extends to a homomorphic section of `q`. -/
theorem exists_section_extending
    {E : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom E.X.hom]
    (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (hflat : Flat q.hom.hom.left) (hsurj : Surjective q.hom.hom.left)
    (a : kernel q ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1) (ha : IsClosedSubgroup a)
    (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))
    (b : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp (kernel q))
    (hconj : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (x : T ⟶ (kernel q).X),
      b.act (g ≫ q.hom.hom) x ≫ (kernelι q).hom.hom = g * (x ≫ (kernelι q).hom.hom) * g⁻¹)
    (hlin : ∀ (T : Over (Spec (CommRingCat.of k)))
      (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) (x : T ⟶ (kernel q).X),
      b.act d x ≫ a.hom.hom = (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom))
    (ι₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶
      (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (hrel : RelativeSolvable ι₁ a χ)
    (σ₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶ E)
    (hσ₁ : σ₁ ≫ q = ι₁) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E,
      s ≫ q = 𝟙 _ ∧ ι₁ ≫ s = σ₁ := by
  have : IsAffine (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.left :=
    isAffine_of_isAffineHom (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.hom
  have : IsAffine E.X.left := isAffine_of_isAffineHom E.X.hom
  have : IsAffineHom q.hom.hom.left := isAffineHom_of_isAffine _
  have : Flat q.hom.hom.left := hflat
  have : Surjective q.hom.hom.left := hsurj
  obtain ⟨fE, hfE⟩ := exists_equivariant q a χ hflat hsurj
  have hc₁ : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ E.X),
      cd ((g * h) ≫ crossedHom q a χ b fE hconj hlin hfE) =
        cd (g ≫ crossedHom q a χ b fE hconj hlin hfE) +
          chi q χ g * cd (h ≫ crossedHom q a χ b fE hconj hlin hfE) := by
    intro T g h
    have := congrArg (fun m => cd (lift g h ≫ m)) (crossedHom_mul q a χ b fE hconj hlin hfE)
    rw [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_mul, cd_mul,
      AutomorphicAction.naturality, cd_act, lift_fst_assoc, lift_fst_assoc,
      lift_snd_assoc] at this
    exact this
  have hc₂ : ∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ (kernel q).X),
      cd ((u ≫ (kernelι q).hom.hom) ≫ crossedHom q a χ b fE hconj hlin hfE) =
        cd (u ≫ a.hom.hom) := by
    intro T u
    rw [Category.assoc, kernel_comp_crossedHom q a χ b fE hconj hlin hfE ha]
  have hι : σ₁.hom.hom ≫ q.hom.hom = ι₁.hom.hom := by
    rw [← Grp.comp_hom_hom, hσ₁]
  obtain ⟨c, h₁, h₂, h₃, h₄⟩ := exists_corrected_relative q a χ b hlin ha σ₁
    (by simpa only [hι] using hrel.1) (by simpa only [hι] using hrel.2) _ hc₁ hc₂
  obtain ⟨s, hs, hvan⟩ := exists_section_vanishing q a χ b hlin c h₁ h₂ ha h₃
  refine ⟨s, hs, ?_⟩
  rw [← hσ₁]
  apply Grp.hom_ext
  change σ₁.hom.hom ≫ q.hom.hom ≫ s.hom.hom = σ₁.hom.hom
  apply eq_of_cd_eq_zero q a χ c h₁ h₂ ha
  · have hsq : s.hom.hom ≫ q.hom.hom = 𝟙 _ := by
      rw [← Grp.comp_hom_hom, hs, Grp.id_hom_hom]
    rw [Category.assoc, Category.assoc, hsq, Category.comp_id]
  · exact hvan _ σ₁.hom.hom
  · simpa only [Category.id_comp] using h₄ _ (𝟙 _)

variable (k Λ) in
/-- One-step splitting compatible with partial sections over `ι₁`, for a fixed field. -/
def OneStepSplittingRel
    (ι₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶
      (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp) : Prop :=
  ∀ (E : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType E.X.hom] [IsAffineHom E.X.hom]
    (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
    Flat q.hom.hom.left → Surjective q.hom.hom.left →
    LocallyOfFinitePresentation q.hom.hom.left →
    ∀ (a : kernel q ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1), IsClosedSubgroup a →
    ∀ (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))
      (b : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp (kernel q)),
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (x : T ⟶ (kernel q).X),
        b.act (g ≫ q.hom.hom) x ≫ (kernelι q).hom.hom =
          g * (x ≫ (kernelι q).hom.hom) * g⁻¹) →
      (∀ (T : Over (Spec (CommRingCat.of k)))
        (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) (x : T ⟶ (kernel q).X),
        b.act d x ≫ a.hom.hom =
          (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom)) →
      ∀ (σ₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶ E), σ₁ ≫ q = ι₁ →
        ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E,
          s ≫ q = 𝟙 _ ∧ ι₁ ≫ s = σ₁

/-- `OneStepSplittingRel` holds when `RelativeSolvable` holds for every closed subgroup of
`𝔾ₐ` whose range is stable under the weight action. -/
theorem oneStepSplittingRel_of
    (ι₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶
      (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (h : ∀ {K : GroupScheme (Spec (CommRingCat.of k))}
      (a : K ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
      (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ)),
      IsClosedSubgroup a →
      (∀ (T : Over (Spec (CommRingCat.of k)))
        (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X)
        (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        x ∈ (SubgroupFunctor.range a).carrier T →
          (VectorGroup.weightAction (n := 1) χ).act d x ∈
            (SubgroupFunctor.range a).carrier T) →
      RelativeSolvable ι₁ a χ) :
    OneStepSplittingRel k Λ ι₁ := by
  intro E _ _ q hflat hsurj _ a ha χ b hconj hlin σ₁ hσ₁
  exact exists_section_extending q hflat hsurj a ha χ b hconj hlin ι₁
    (h a χ ha fun T d x hx => weight_stable q a χ b hlin (T := T) d x hx) σ₁ hσ₁

/-- One step of a tower, compatibly with a partial section over `ι₁`. -/
theorem exists_section_of_step_rel
    {ι₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶
      (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp}
    (hsplit : OneStepSplittingRel k Λ ι₁)
    {E Q : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType E.X.hom] [IsAffineHom E.X.hom] [IsAffineHom Q.X.hom]
    (p : E ⟶ Q) (r : Q ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι p)) p)
    (hK : IsCharacterLinearKernel (Diagonalizable.groupScheme (CommRingCat.of k) Λ) (p ≫ r) p)
    (t : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ Q) (ht : t ≫ r = 𝟙 _)
    (σ₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶ E)
    (hσ₁ : σ₁ ≫ p = ι₁ ≫ t) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E,
      s ≫ p ≫ r = 𝟙 _ ∧ ι₁ ≫ s = σ₁ := by
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
  have hinvincl :
      (kernelι π).hom.hom ≫ incl.hom.hom = e.inv.hom.hom ≫ (kernelι p).hom.hom := by
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
  -- The partial section in the inverse image.
  let σ₁' :
      (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶ SubgroupPreimage.groupScheme p t :=
    pullback.lift σ₁ ι₁ hσ₁
  have hσ₁incl : σ₁' ≫ incl = σ₁ := pullback.lift_fst _ _ _
  have hσ₁π : σ₁' ≫ π = ι₁ := pullback.lift_snd _ _ _
  obtain ⟨s', hs', hs'σ⟩ := hsplit (SubgroupPreimage.groupScheme p t) π hπ.1 hπ.2.1 hπ.2.2.1
    (e.inv ≫ a) ha' χ (b.transportActed e)
    (by
      intro T g x
      apply (cancel_mono incl.hom.hom).mp
      have h1 :
          e.hom.hom.hom ≫ (kernelι π).hom.hom ≫ incl.hom.hom = (kernelι p).hom.hom := by
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
    σ₁' hσ₁π
  refine ⟨s' ≫ incl, ?_, ?_⟩
  · rw [Category.assoc, hπt, hs']
  · rw [← Category.assoc, hs'σ, hσ₁incl]

/-- Every finite character-linear kernel tower has a homomorphic section extending a given
partial section over `ι₁`, given `OneStepSplittingRel k Λ ι₁`. -/
theorem exists_section_of_hasTower_rel
    {ι₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶
      (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp}
    (hsplit : OneStepSplittingRel k Λ ι₁) :
    ∀ (n : ℕ) {E : GroupScheme (Spec (CommRingCat.of k))}
      (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
      HasTower (Diagonalizable.groupScheme (CommRingCat.of k) Λ) n q →
      ∀ (σ₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶ E), σ₁ ≫ q = ι₁ →
        ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E,
          s ≫ q = 𝟙 _ ∧ ι₁ ≫ s = σ₁
  | 0, E, q, h, σ₁, hσ₁ => by
    have : IsIso q := h.2.2
    refine ⟨inv q, IsIso.inv_hom_id q, ?_⟩
    rw [← hσ₁, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  | n + 1, E, q, h, σ₁, hσ₁ => by
    obtain ⟨hft, haff, Q, p, r, hp, hpr, hK, hr⟩ := h
    have : LocallyOfFiniteType E.X.hom := hft
    have : IsAffineHom E.X.hom := haff
    have : IsAffineHom Q.X.hom := hr.isAffineHom
    subst hpr
    obtain ⟨t, ht, htσ⟩ := exists_section_of_hasTower_rel hsplit n r hr (σ₁ ≫ p)
      (by rw [Category.assoc, hσ₁])
    exact exists_section_of_step_rel hsplit p r hp hK t ht σ₁ htσ.symm

/-- A homomorphism admitting a finite character-linear kernel tower has a homomorphic section
extending a given partial section over `ι₁`, given `OneStepSplittingRel k Λ ι₁`. -/
theorem exists_section_of_admitsTower_rel
    {ι₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶
      (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp}
    (hsplit : OneStepSplittingRel k Λ ι₁)
    {E : GroupScheme (Spec (CommRingCat.of k))}
    {q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp}
    (h : AdmitsTower (Diagonalizable.groupScheme (CommRingCat.of k) Λ) q)
    (σ₁ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).toGrp ⟶ E)
    (hσ₁ : σ₁ ≫ q = ι₁) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E,
      s ≫ q = 𝟙 _ ∧ ι₁ ≫ s = σ₁ := by
  obtain ⟨n, hn⟩ := h
  exact exists_section_of_hasTower_rel hsplit n q hn σ₁ hσ₁

end Langlands.GroupScheme.TrigonalizableExtensionSplit
