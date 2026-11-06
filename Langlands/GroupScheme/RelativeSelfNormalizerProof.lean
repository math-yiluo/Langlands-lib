import Langlands.GroupScheme.RelativeSelfNormalizerStatement
import Langlands.GroupScheme.RelativeSelfNormalizer.SquareZero
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.CorepresentedSmooth
import Mathlib.RingTheory.Smooth.Flat

/-! # Field-fibre detection of relative self-normalization

A smooth closed subgroup `H` of a smooth affine group `G` over a scheme `S` is self-normalizing
on all tests as soon as this holds after every field-valued base change `Spec k ⟶ S`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S S' : Scheme.{u}} {G G' H : GroupScheme S}

/-- The inclusion of the normalizer of `range i` in `range i` on one test transfers along an
isomorphism of tests. -/
theorem normalizer_carrier_le_of_iso (i : H ⟶ G) {T T' : Over S} (ε : T ≅ T')
    (h : (range i).normalizer.carrier T ≤ (range i).carrier T) :
    (range i).normalizer.carrier T' ≤ (range i).carrier T' := by
  intro x hx
  have h1 := (range i).comp_mem ε.inv (h ((range i).normalizer.comp_mem ε.hom hx))
  rwa [← Category.assoc, ε.inv_hom_id, Category.id_comp] at h1

theorem comp_inv_hom_comp_hom (e : G ≅ G') {T : Over S} (g : T ⟶ G'.X) :
    (g ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = g :=
  comp_hom_comp_inv_hom e.symm g

/-- A point lies in `range i` exactly when its image under an isomorphism `e` lies in
`range (i ≫ e.hom)`. -/
theorem mem_range_comp_iso_iff (i : H ⟶ G) (e : G ≅ G') {T : Over S} (x : T ⟶ G.X) :
    x ≫ e.hom.hom.hom ∈ (range (i ≫ e.hom)).carrier T ↔ x ∈ (range i).carrier T := by
  rw [mem_range, mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have h := congrArg (· ≫ e.inv.hom.hom) hy
    simp only at h
    rw [comp_hom_comp_inv_hom, Grp.comp_hom_hom, ← Category.assoc, comp_hom_comp_inv_hom] at h
    exact h
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Grp.comp_hom_hom, Category.assoc]⟩

/-- Self-normalization on one test is invariant under an isomorphism of the ambient group. -/
theorem normalizer_carrier_le_iff_of_iso (i : H ⟶ G) (e : G ≅ G') (T : Over S) :
    (range (i ≫ e.hom)).normalizer.carrier T ≤ (range (i ≫ e.hom)).carrier T ↔
      (range i).normalizer.carrier T ≤ (range i).carrier T := by
  constructor
  · intro h x hx
    rw [normalizer_range_eq_comap_of_iso i e, mem_comap] at hx
    exact (mem_range_comp_iso_iff i e x).1 (h hx)
  · intro h x hx
    have hx' : x ≫ e.inv.hom.hom ∈ (range i).normalizer.carrier T := by
      rw [normalizer_range_eq_comap_of_iso i e, mem_comap, comp_inv_hom_comp_hom e x]
      exact hx
    have h1 := (mem_range_comp_iso_iff i e _).2 (h hx')
    rwa [comp_inv_hom_comp_hom e x] at h1

/-- Self-normalization on a test over `S'` after base change along `b : S' ⟶ S` is
self-normalization on the same test regarded over `S`. -/
theorem normalizer_carrier_le_iff_baseChange (b : S' ⟶ S) (i : H ⟶ G) (T : Over S') :
    (range ((GroupScheme.baseChange b).map i)).normalizer.carrier T ≤
        (range ((GroupScheme.baseChange b).map i)).carrier T ↔
      (range i).normalizer.carrier ((Over.map b).obj T) ≤
        (range i).carrier ((Over.map b).obj T) := by
  rw [range_baseChangeHom, ← normalizer_baseChange]
  constructor
  · intro h x hx
    have h1 : (baseChangePointsEquiv b G T).symm x ∈ ((range i).baseChange b).carrier T := by
      apply h
      rw [mem_baseChange, MulEquiv.apply_symm_apply]
      exact hx
    rwa [mem_baseChange, MulEquiv.apply_symm_apply] at h1
  · intro h x hx
    exact h hx

/-- The field hypothesis of the target gives self-normalization on every test whose structure
map factors through a field-valued point of `S`. -/
theorem normalizer_carrier_le_of_fieldPoint (i : H ⟶ G)
    (hfield : ∀ (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S),
      (range ((GroupScheme.baseChange b).map i)).normalizer =
        range ((GroupScheme.baseChange b).map i))
    (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (T : Over (Spec (CommRingCat.of k))) :
    (range i).normalizer.carrier ((Over.map b).obj T) ≤
      (range i).carrier ((Over.map b).obj T) :=
  (normalizer_carrier_le_iff_baseChange b i T).1
    (le_of_eq (congrArg (fun F => F.carrier T) (hfield k b)))

/-- Membership in the range of a monomorphism can be checked on the affine open cover of the
test scheme. -/
theorem mem_range_of_affineCover (i : H ⟶ G) [Mono i.hom.hom] {T : Over S} (x : T ⟶ G.X)
    (h : ∀ j : T.left.affineCover.I₀,
      (Over.homMk (T.left.affineCover.f j) rfl :
          Over.mk (T.left.affineCover.f j ≫ T.hom) ⟶ T) ≫ x ∈
        (range i).carrier (Over.mk (T.left.affineCover.f j ≫ T.hom))) :
    x ∈ (range i).carrier T := by
  let 𝒰 := T.left.affineCover
  choose y hy using fun j => mem_range.1 (h j)
  let V : Over S := Over.mk (Sigma.desc 𝒰.f ≫ T.hom)
  let q : V ⟶ T := Over.homMk (Sigma.desc 𝒰.f) rfl
  -- Instance search does not find this instance through the `outParam` of `HasRingHomProperty`.
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  have : LocallyOfFinitePresentation (Sigma.desc 𝒰.f) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance
  have : EffectiveEpi q.left := by
    change EffectiveEpi (Sigma.desc 𝒰.f)
    infer_instance
  apply mem_range_of_comp_mem_range i q
  refine mem_range.2 ⟨Over.homMk (Sigma.desc fun j => (y j).left) ?_, ?_⟩
  · apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_comp_desc_assoc]
    change (y j).left ≫ H.X.hom = Sigma.ι 𝒰.X j ≫ Sigma.desc 𝒰.f ≫ T.hom
    rw [Sigma.ι_comp_desc_assoc]
    exact Over.w (y j)
  · apply Over.OverMorphism.ext
    apply Sigma.hom_ext
    intro j
    change Sigma.ι 𝒰.X j ≫ Sigma.desc (fun j => (y j).left) ≫ i.hom.hom.left =
      Sigma.ι 𝒰.X j ≫ Sigma.desc 𝒰.f ≫ x.left
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc]
    exact congrArg CommaMorphism.left (hy j)

end SubgroupFunctor

namespace Corepresented

open SubgroupFunctor

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}

/-- **The corepresented case.** For a smooth closed subgroup `j` of a smooth corepresented
affine group over `Spec R`, self-normalization on all spectra of `R`-algebras follows from
self-normalization on spectra of `R`-algebras whose structure map factors through a field. -/
theorem normalizer_carrier_le_of_field {K : GroupScheme (Spec R)} (j : K ⟶ groupScheme F e)
    (hj : IsClosedSubgroup j) (hG : Smooth (groupScheme F e).X.hom) (hK : Smooth K.X.hom)
    (hfield : ∀ (E : CommAlgCat.{u} R) (k : Type u) [Field k] (ρ : R →+* k) (φ : k →+* E),
      φ.comp ρ = algebraMap R E →
        (range j).normalizer.carrier ((algSpec R).obj (op E)) ≤
          (range j).carrier ((algSpec R).obj (op E)))
    (A : CommAlgCat.{u} R) :
    (range j).normalizer.carrier ((algSpec R).obj (op A)) ≤
      (range j).carrier ((algSpec R).obj (op A)) := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  obtain ⟨I, hI⟩ := exists_ideal_range j
  have hcut := isCutOutBy_range hI
  -- `K` is isomorphic to the cut-out group scheme `Spec (B ⧸ I)`, so `B ⧸ I` is smooth.
  have hrange : range j = range (cutHom hcut) := by
    rw [range_cutHom]
    exact SubgroupFunctor.ext fun T => Subgroup.ext fun x => mem_range_iff_mem_affineSubgroups hI x
  let hr : (range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  let hr' : (range j).IsRepresentedBy (cutHom hcut) := ⟨inferInstance, hrange.symm⟩
  let ε : K ≅ cutGroupScheme hcut := hr.isoOfIsRepresentedBy hr'
  have hsmooth : Smooth (cutGroupScheme hcut).X.hom := by
    have : IsIso ε.inv.hom.hom.left :=
      (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso ε.symm)).hom)
    rw [← Over.w ε.inv.hom.hom]
    infer_instance
  have hBI : Algebra.Smooth R (B ⧸ I) := smooth_groupScheme_iff.1 hsmooth
  have hB : Algebra.Smooth R B := smooth_groupScheme_iff.1 hG
  have hIfg : I.FG := by
    have h := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ R I)
      Ideal.Quotient.mk_surjective
    rwa [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker] at h
  have hmain := normalizerFamily_le_of_field hcut hIfg (fun E k _ ρ φ hρφ g hg => by
    rw [← affineSubgroups_normalizer hI] at hg
    exact hfield E k ρ φ hρφ hg) A
  intro x hx
  have h1 : affinePointsEquiv F e A x ∈ normalizerFamily (affineSubgroups (range j)) A := by
    rw [← affineSubgroups_normalizer hI]
    show (affinePointsEquiv F e A).symm (affinePointsEquiv F e A x) ∈
      (range j).normalizer.carrier ((algSpec R).obj (op A))
    rwa [MulEquiv.symm_apply_apply]
  have h2 := hmain h1
  change (affinePointsEquiv F e A).symm (affinePointsEquiv F e A x) ∈
    (range j).carrier ((algSpec R).obj (op A)) at h2
  rwa [MulEquiv.symm_apply_apply] at h2

end Corepresented

namespace SubgroupFunctor

/-- **The affine case.** Over an affine base `Spec R`, for a smooth closed subgroup of a smooth
group with affine total space, self-normalization on the spectra of all `R`-algebras follows
from self-normalization on the spectra of `R`-algebras over fields. -/
theorem normalizer_carrier_le_of_affine {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    [IsAffine G.X.left] (i : H ⟶ G) (hi : IsClosedSubgroup i) (hG : Smooth G.X.hom)
    (hH : Smooth H.X.hom)
    (hfield : ∀ (E : CommAlgCat.{u} R) (k : Type u) [Field k] (ρ : R →+* k) (φ : k →+* E),
      φ.comp ρ = algebraMap R E →
        (range i).normalizer.carrier ((algSpec R).obj (op E)) ≤
          (range i).carrier ((algSpec R).obj (op E)))
    (A : CommAlgCat.{u} R) :
    (range i).normalizer.carrier ((algSpec R).obj (op A)) ≤
      (range i).carrier ((algSpec R).obj (op A)) := by
  let c := (AffineCoordinates.groupSchemeIso G).symm
  rw [← normalizer_carrier_le_iff_of_iso i c]
  have : IsClosedImmersion i.hom.hom.left := hi
  refine Corepresented.normalizer_carrier_le_of_field (i ≫ c.hom) ?_ ?_ hH ?_ A
  · exact (inferInstance : IsClosedImmersion (AffineCoordinates.coordinateHom i).hom.hom.left)
  · rw [Corepresented.smooth_groupScheme_iff]
    exact AffineCoordinates.smooth_algebra G hG
  · intro E k _ ρ φ h
    rw [normalizer_carrier_le_iff_of_iso i c]
    exact hfield E k ρ φ h

/-- **Affine tests.** Under the field-point condition, the normalizer of a smooth closed subgroup
of a smooth affine group lies in the subgroup on every test with affine total space. -/
theorem normalizer_carrier_le_of_isAffine {S : Scheme.{u}} {G H : GroupScheme S}
    [IsAffineHom G.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i) (hG : Smooth G.X.hom)
    (hH : Smooth H.X.hom)
    (hS : ∀ (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
      (T : Over (Spec (CommRingCat.of k))),
      (range i).normalizer.carrier ((Over.map b).obj T) ≤
        (range i).carrier ((Over.map b).obj T))
    (T : Over S) (hT : IsAffine T.left) :
    (range i).normalizer.carrier T ≤ (range i).carrier T := by
  let A : CommRingCat.{u} := Γ(T.left, ⊤)
  let f : Spec A ⟶ S := T.left.isoSpec.inv ≫ T.hom
  have : IsAffine ((GroupScheme.baseChange f).obj G).X.left := by
    change IsAffine (pullback G.X.hom f)
    infer_instance
  have hG' : Smooth ((GroupScheme.baseChange f).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom f)
    infer_instance
  have hH' : Smooth ((GroupScheme.baseChange f).obj H).X.hom := by
    change Smooth (pullback.snd H.X.hom f)
    infer_instance
  have key := normalizer_carrier_le_of_affine ((GroupScheme.baseChange f).map i)
    (IsClosedSubgroup.baseChange f hi) hG' hH' (fun E k _ ρ φ hρφ => by
      apply (normalizer_carrier_le_iff_baseChange f i _).2
      refine normalizer_carrier_le_of_iso i ?_
        (hS k (Spec.map (CommRingCat.ofHom ρ) ≫ f) (Over.mk (Spec.map (CommRingCat.ofHom φ))))
      refine Over.isoMk (Iso.refl _) ((Category.id_comp _).trans ?_)
      change Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ f =
        Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ρ) ≫ f
      rw [← Category.assoc (Spec.map (CommRingCat.ofHom φ)), ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hρφ])
    (CommAlgCat.of A A)
  refine normalizer_carrier_le_of_iso i ?_ ((normalizer_carrier_le_iff_baseChange f i _).1 key)
  refine Over.isoMk T.left.isoSpec.symm ?_
  rw [Over.map_obj_hom, algSpec_obj_hom, Iso.symm_hom, Algebra.algebraMap_self,
    CommRingCat.ofHom_id, Spec.map_id]
  exact (Category.id_comp f).symm

end SubgroupFunctor

open SubgroupFunctor in
/-- **Field-fibre detection of relative self-normalization** (Conrad, *Reductive group
schemes*, Proposition 2.1.6 and Lemma B.3.1). -/
theorem relativeSelfNormalizer : RelativeSelfNormalizerStatement.{u} := by
  intro S G H _ _ i hi hH _ hfield
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  refine le_antisymm (fun T x hx => ?_) (le_normalizer _)
  apply mem_range_of_affineCover i x
  intro j
  exact normalizer_carrier_le_of_isAffine i hi ‹_› hH
    (normalizer_carrier_le_of_fieldPoint i hfield) _ (Scheme.isAffine_affineCover _ j)
    ((range i).normalizer.comp_mem _ hx)

end Langlands.GroupScheme
