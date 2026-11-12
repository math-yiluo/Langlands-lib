import Langlands.GroupScheme.Rational.IsotropicRootSubgroupGenerationStatement
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.GroupScheme.Rational.RelativeRankIdentityProof
import Langlands.GroupScheme.Rational.AnisotropicRootSystem
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.Dynamic.OppositeEnvelope
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-!
# Root subgroups generate an isotropic almost-simple group: proof
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Helpers

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A subgroup functor containing every relative root subgroup contains the dynamic radical of
every cocharacter of a maximal split torus of a connected reductive group. -/
theorem dynamicUnipotent_le_of_rootSubgroups_le (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (F : SubgroupFunctor G)
    (hF : haveI := hG.isAffineHom
      ∀ a ∈ relativeRoots i, RelativeRoot.subgroup i a ≤ F) :
    Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) ≤ F := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hT : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  have hroot : HasRelativeRootSystem i := relativeRootSystem k G hG S i hi
  have hfin : (RelativeRoot.indivisiblePositiveRoots i ν).Finite :=
    (hroot.finite_relativeRoots i hT).subset (fun a ha => ha.1.1)
  have := hfin.to_subtype
  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin (RelativeRoot.indivisiblePositiveRoots i ν)
  let a : Fin n → characterLattice S := fun r => (eqv.symm r).1
  have ha : Function.Injective a := Subtype.val_injective.comp eqv.symm.injective
  have hra : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν := by
    ext x
    constructor
    · rintro ⟨r, rfl⟩
      exact (eqv.symm r).2
    · intro hx
      exact ⟨eqv ⟨x, hx⟩, by simp [a]⟩
  obtain ⟨U, jU, H, j, e, hjU, -, -, -, -, -, hj, he⟩ :=
    RelativeRoot.dynamicRootOrderedProduct k G hG S i hi ν n a ha hra
  intro T g hg
  rw [← hjU.2] at hg
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hg
  have hy : y ≫ jU.hom.hom = (y ≫ e.inv) ≫ RelativeRoot.orderedMultiplication j := by
    rw [← he, Category.assoc, e.inv_hom_id_assoc]
  rw [hy, RelativeRoot.orderedMultiplication]
  let φ : ((∏ᶜ H).X ⟶ G.X) →* (T ⟶ G.X) :=
    MonoidHom.mk' (fun f => (y ≫ e.inv) ≫ f) (fun f f' => MonObj.comp_mul _ f f')
  change φ _ ∈ _
  rw [map_list_prod, List.map_ofFn]
  apply Subgroup.list_prod_mem
  intro z hz
  obtain ⟨r, rfl⟩ := List.mem_ofFn.1 hz
  have hmem : (y ≫ e.inv) ≫ (Limits.Pi.π H r).hom.hom ≫ (j r).hom.hom ∈
      (RelativeRoot.subgroup i (a r)).carrier T := by
    rw [← (hj r).1.2]
    exact SubgroupFunctor.mem_range.2 ⟨_, Category.assoc _ _ _⟩
  have har : a r ∈ relativeRoots i := (eqv.symm r).2.1.1
  exact hF (a r) har T hmem

/-- An isotropic semisimple group has a relative root. -/
theorem IsSemisimple.relativeRoots_nonempty [IsAffineHom G.X.hom] (hG : IsSemisimple G)
    (hani : ¬ IsAnisotropic G) {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) :
    (relativeRoots i).Nonempty := by
  by_contra hne
  have hempty : relativeRoots i = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  obtain ⟨-, -, -, hsr, hrk, -⟩ := relativeRankIdentity k G hG.isConnectedReductive S i hi
  have h1 : relativeRootRank i = 0 := by
    rw [relativeRootRank, relativeRootSpan_eq_bot_of_relativeRoots_eq_empty hempty]
    exact finrank_bot ℚ _
  have hderived : IsDerivedSubgroup (𝟙 G) := by
    refine ⟨IsClosedSubgroup.of_iso (Iso.refl G), ?_⟩
    rw [semisimplePerfect k G hG]
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    simp only [SubgroupFunctor.top_carrier, Subgroup.mem_top, iff_true]
    exact SubgroupFunctor.mem_range.2 ⟨x, by simp⟩
  have hchar : Subsingleton (rationalCharacters G) := by
    constructor
    intro χ ψ
    have hχ := hderived.characterRestrict_eq_zero χ
    have hψ := hderived.characterRestrict_eq_zero ψ
    rw [characterRestrict_id] at hχ hψ
    exact hχ.trans hψ.symm
  have h2 : rationalCharacterRank G = 0 := by
    rw [rationalCharacterRank]
    exact Module.finrank_zero_of_subsingleton
  apply hani
  rw [IsAnisotropic, hsr, hrk, h1, h2]
  rfl

/-- The closed subgroup generated by `U(χ)`, `χ` and `U(χ⁻¹)` in a smooth connected affine
group is normal: it is normalized by `P(χ)` and contains `U(χ⁻¹)`, so its product with `P(χ)`
is smooth and surjective, and the closed normalizer of the subgroup contains this product. -/
theorem Dynamic.OppositeEnvelope.isNormal_range {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] [IsAffine G.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (D : GeneratedImage (Dynamic.OppositeEnvelope.map χ)) [Smooth D.group.X.hom]
    [IsAffineHom D.group.X.hom] :
    (SubgroupFunctor.range D.inclusion).IsNormal := by
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ G.X.hom
  -- the parabolic `P(χ)` normalizes `D`, and `D × P(χ) → G` is smooth surjective
  let P := Dynamic.Affine.parabolicScheme χ
  let ip : P ⟶ G := Dynamic.Affine.parabolicHom χ
  have hiprep : (Dynamic.parabolic χ).IsRepresentedBy ip :=
    Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hipc : IsClosedSubgroup ip := Dynamic.Affine.isClosedSubgroup_parabolicHom χ
  have : Mono ip.hom.hom := hiprep.1
  have : Smooth P.X.hom := (dynamicSmooth k G χ P ip).1 hiprep
  have : IsAffineHom P.X.hom := by
    have : IsClosedImmersion ip.hom.hom.left := hipc
    rw [← Over.w ip.hom.hom]
    infer_instance
  have hDnP := Dynamic.OppositeEnvelope.isNormalizedBy_parabolic D
  have hnorm' : (SubgroupFunctor.range D.inclusion).IsNormalizedBy (SubgroupFunctor.range ip) := by
    rw [hiprep.2]
    exact hDnP
  obtain ⟨-, hsurj⟩ := Dynamic.normalized_subgroup_product_smooth_surjective D.inclusion ip χ
    D.closed hnorm' (Dynamic.OppositeEnvelope.reversed_unipotent_le D) (le_of_eq hiprep.2.symm)
  -- the normalizer of `D` is closed and contains the image of the multiplication
  obtain ⟨⟨C, c, hcc, hcrep⟩, -⟩ :=
    hasClosedRepresentative_normalizer_centralizer_range D.inclusion D.closed
  let m : D.group.X ⊗ P.X ⟶ G.X :=
    (fst D.group.X P.X ≫ D.inclusion.hom.hom) * (snd D.group.X P.X ≫ ip.hom.hom)
  have hmN : m ∈ (SubgroupFunctor.range D.inclusion).normalizer.carrier (D.group.X ⊗ P.X) := by
    apply mul_mem
    · rw [SubgroupFunctor.mem_normalizer]
      intro V a x hx
      have ha : a ≫ fst D.group.X P.X ≫ D.inclusion.hom.hom ∈
          (SubgroupFunctor.range D.inclusion).carrier V :=
        SubgroupFunctor.mem_range.2 ⟨a ≫ fst _ _, Category.assoc _ _ _⟩
      exact ⟨mul_mem (mul_mem ha hx) (inv_mem ha), mul_mem (mul_mem (inv_mem ha) hx) ha⟩
    · rw [SubgroupFunctor.mem_normalizer]
      intro V a x hx
      have ha : a ≫ snd D.group.X P.X ≫ ip.hom.hom ∈ (Dynamic.parabolic χ).carrier V := by
        rw [← hiprep.2]
        exact SubgroupFunctor.mem_range.2 ⟨a ≫ snd _ _, Category.assoc _ _ _⟩
      refine ⟨hDnP V _ x ha hx, ?_⟩
      have := hDnP V _ x (inv_mem ha) hx
      rwa [inv_inv] at this
  rw [← hcrep.2] at hmN
  obtain ⟨m', hm'⟩ := SubgroupFunctor.mem_range.1 hmN
  have : IsClosedImmersion c.hom.hom.left := hcc
  have : Surjective m.left := hsurj
  have : IsSchemeTheoreticallyDominant m.left := IsSchemeTheoreticallyDominant.of_isDominant _
  obtain ⟨f', hf'⟩ := exists_lift_of_isSchemeTheoreticallyDominant c.hom.hom.left
    (𝟙 G.X.left) m.left m'.left (by
      rw [Category.comp_id, ← Over.comp_left, hm'])
  let f'' : G.X ⟶ C.X := Over.homMk f' (by
    rw [← Over.w c.hom.hom, ← Category.assoc, hf', Category.id_comp])
  have hNtop : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      g ∈ (SubgroupFunctor.range D.inclusion).normalizer.carrier T := by
    intro T g
    rw [← hcrep.2]
    refine SubgroupFunctor.mem_range.2 ⟨g ≫ f'', ?_⟩
    rw [Category.assoc]
    have : f'' ≫ c.hom.hom = 𝟙 G.X := by
      ext
      exact hf'
    rw [this, Category.comp_id]
  intro T g x _ hx
  have := (SubgroupFunctor.mem_normalizer.1 (hNtop T g)) T (𝟙 T) x hx
  simpa only [Category.id_comp] using this.1

end Helpers

/-- In an isotropic almost-simple group, a closed subgroup containing a maximal split torus and
every relative root subgroup is the whole group. -/
theorem isotropicRootSubgroupGeneration : IsotropicRootSubgroupGenerationStatement.{u} := by
  intro k _ G _ hG hani S i hi H h hhc hiH hrootH
  have hGred := hG.isSemisimple.isConnectedReductive
  have : Smooth G.X.hom := hGred.smooth
  have : ConnectedSpace G.X.left := hGred.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hT : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  obtain ⟨ν, hν⟩ := hT.exists_genericCocharacter i
  let χ := CommGroupScheme.groupHom ν ≫ i
  have hUle : ∀ ν' : cocharacterLattice S,
      Dynamic.unipotent (CommGroupScheme.groupHom ν' ≫ i) ≤ SubgroupFunctor.range h :=
    fun ν' => dynamicUnipotent_le_of_rootSubgroups_le hGred hi ν' _ hrootH
  have hrev : Dynamic.OppositeEnvelope.reversed χ = CommGroupScheme.groupHom (-ν) ≫ i := by
    have hneg : Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ ν = -ν := by
      rw [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
    rw [← hneg]
    apply hom_ext_points
    intro U x
    simp only [χ, Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_comp]
  have hUrev : Dynamic.unipotent (Dynamic.OppositeEnvelope.reversed χ) ≤
      SubgroupFunctor.range h := by
    rw [hrev]
    exact hUle (-ν)
  -- the closed subgroup `D` generated by `U(χ)`, `χ` and `U(χ⁻¹)`
  obtain ⟨D, hDs, hDa, hDgc, -⟩ := Dynamic.OppositeEnvelope.exists_generatedImage χ
  have : Smooth D.group.X.hom := hDs
  have : IsAffineHom D.group.X.hom := hDa
  have : GeometricallyConnected D.group.X.hom := hDgc
  have hDc : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  -- `D` lies in `H`
  have hDH : SubgroupFunctor.range D.inclusion ≤ SubgroupFunctor.range h := by
    apply D.range_le h hhc
    rw [factorsThrough_iff_containsImage, SubgroupFunctor.containsImage_iff]
    have hm := Dynamic.OppositeEnvelope.comp_map χ (𝟙 _)
    simp only [Category.id_comp] at hm
    rw [hm]
    refine mul_mem (mul_mem ?_ ?_) ?_
    · apply hUle ν
      rw [← (Dynamic.Affine.isRepresentedBy_unipotentHom χ).2]
      exact SubgroupFunctor.mem_range.2 ⟨_, rfl⟩
    · apply hiH
      exact SubgroupFunctor.mem_range.2 ⟨snd _ _ ≫ fst _ _ ≫ (CommGroupScheme.groupHom ν).hom.hom,
        by simp only [χ, Grp.comp_hom_hom, Category.assoc]⟩
    · apply hUrev
      rw [← (Dynamic.Affine.isRepresentedBy_unipotentHom _).2]
      exact SubgroupFunctor.mem_range.2 ⟨snd _ _ ≫ snd _ _, Category.assoc _ _ _⟩
  have hDnormal := Dynamic.OppositeEnvelope.isNormal_range χ D
  -- almost simplicity
  rcases hG.normalSubgroup_trivial_or_full D.group D.inclusion D.closed hDs hDc hDnormal with
    hbot | htop
  · exfalso
    obtain ⟨r, hr⟩ := hG.isSemisimple.relativeRoots_nonempty hani hi
    have hχ1 : χ.hom.hom = 1 := by
      have h1 := Dynamic.OppositeEnvelope.range_cocharacter_le D _
        (SubgroupFunctor.mem_range.2 ⟨𝟙 _, Category.id_comp _⟩)
      rw [hbot] at h1
      simpa using h1
    have : Mono i.hom.hom := Over.mono_of_mono_left _
    have hν0 : ν = 0 := by
      apply CommGroupScheme.hom_ext_points
      intro U x
      apply (cancel_mono i.hom.hom).1
      have h1 : x ≫ χ.hom.hom = 1 := by rw [hχ1, MonObj.comp_one]
      simp only [χ, Grp.comp_hom_hom] at h1
      rw [Category.assoc, h1, comp_groupHom_zero, MonObj.one_comp]
    exact hν r hr (by rw [hν0, map_zero])
  · apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    simp only [SubgroupFunctor.top_carrier, Subgroup.mem_top, iff_true]
    apply hDH T
    rw [htop]
    trivial

end Langlands.GroupScheme
