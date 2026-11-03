import Langlands.GroupScheme.CorepresentedNormalizer
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.AlgebraicGeometry.ProjectiveTensorClosedLocus

/-! # Closed representability of normalizers and centralizers of closed subgroups

For a closed subgroup `j : K ⟶ Spec B` of a corepresented affine group scheme, the subgroup
functors `(range j).normalizer` and `(range j).centralizer` are represented on every test
scheme by the closed subgroup schemes cut out by `subgroupNormalizerIdeal` and `subgroupCentralizerIdeal`,
provided `B ⧸ I` is projective over the base, where `I` is the ideal of `K`. Over a field this
applies to every closed subgroup of every affine group scheme.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}

section AffineTests

/-- If the subgroups of `F` given by the points of `K` over the spectra of algebras are cut out by
`J`, then `K` is cut out by `J` on all affine test schemes, whatever their structure maps. -/
theorem isAffineCutOutBy_of_isCutOutBy {K : SubgroupFunctor (groupScheme F e)} {J : Ideal B}
    (hK : IsCutOutBy e (affineSubgroups K) J) : IsAffineCutOutBy e K J := by
  intro A f x
  let _ : Algebra R A := (Spec.preimage f).hom.toAlgebra
  let A' : CommAlgCat.{u} R := CommAlgCat.of R A
  have hf : ((algSpec R).obj (op A')).hom = f := by
    rw [algSpec_obj_hom]
    exact Spec.map_preimage f
  let ε : (algSpec R).obj (op A') ≅ Over.mk f :=
    Over.isoMk (Iso.refl _) ((Category.id_comp _).trans hf.symm)
  have hmem : x ∈ K.carrier (Over.mk f) ↔ ε.hom ≫ x ∈ K.carrier ((algSpec R).obj (op A')) :=
    ⟨fun h => K.comp_mem _ h, fun h => by simpa using K.comp_mem ε.inv h⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : B ⟶ A', (algSpec R).map ψ.op = ε.hom ≫ x :=
    ⟨(algSpec.fullyFaithful.preimage (X := op A') (Y := op B) (ε.hom ≫ x)).unop,
      algSpec.fullyFaithful.map_preimage _⟩
  have hleft : x.left = ((algSpec R).map ψ.op).left := by
    rw [hψ, Over.comp_left]
    exact (Category.id_comp _).symm
  have h2 : pointRing x = CommRingCat.ofHom (ψ.hom.toRingHom : B →+* A) :=
    Spec.map_injective ((specMap_pointRing x).trans (hleft.trans rfl))
  rw [hmem]
  have h0 : affinePointsEquiv F e A' (ε.hom ≫ x) = e.homEquiv ψ :=
    (congrArg (affinePointsEquiv F e A') hψ).symm.trans (affinePointsEquiv_map F e A' ψ)
  have h1 : ε.hom ≫ x ∈ K.carrier ((algSpec R).obj (op A')) ↔
      e.homEquiv ψ ∈ affineSubgroups K A' := by
    change _ ↔ (affinePointsEquiv F e A').symm (e.homEquiv ψ) ∈ K.carrier _
    rw [← h0, MulEquiv.symm_apply_apply]
  rw [h1, hK, Equiv.symm_apply_apply, h2]
  rfl

end AffineTests

section Range

/-- The points of a closed subgroup scheme of `Spec B` over an arbitrary test scheme are the
points whose classifying algebra map kills a fixed ideal of `B`. -/
theorem exists_ideal_range {K : GroupScheme (Spec R)} (j : K ⟶ groupScheme F e)
    [hj : IsClosedImmersion j.hom.hom.left] :
    ∃ I : Ideal B, ∀ (U : Over (Spec R)) (y : U ⟶ (groupScheme F e).X),
      y ∈ (SubgroupFunctor.range j).carrier U ↔
        ∀ b ∈ I, (e.homEquiv.symm (pointsEquiv F e U y)).hom b = 0 := by
  have hj' : IsClosedImmersion (j.hom.hom.left : K.X.left ⟶ Spec (CommRingCat.of B)) := hj
  obtain ⟨I, ε, hε⟩ := (IsClosedImmersion.Spec_iff (R := CommRingCat.of B)
    (f := j.hom.hom.left)).1 hj'
  refine ⟨I, fun U y => ?_⟩
  simp only [homEquiv_symm_pointsEquiv_apply]
  have hfac := Langlands.AlgebraicGeometry.factorsThrough_affineQuotient_iff I (y.left : U.left ⟶ Spec (CommRingCat.of B))
  rw [SubgroupFunctor.mem_range]
  refine Iff.trans ?_ (hfac.trans ⟨fun h b hb => h hb, fun h b hb => h b hb⟩)
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t.left ≫ ε.hom, ?_⟩
    rw [Category.assoc, ← hε]
    rfl
  · rintro ⟨z, hz⟩
    have hw : K.X.hom = j.hom.hom.left ≫ (groupScheme F e).X.hom := (Over.w j.hom.hom).symm
    have h3 : ε.inv ≫ j.hom.hom.left = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
      (ε.inv ≫= hε).trans (Iso.inv_hom_id_assoc ε _)
    have h4 : (z ≫ ε.inv) ≫ j.hom.hom.left = y.left :=
      (Category.assoc _ _ _).trans ((z ≫= h3).trans hz)
    refine ⟨Over.homMk (z ≫ ε.inv) ?_, ?_⟩
    · change (z ≫ ε.inv) ≫ K.X.hom = U.hom
      rw [hw, ← Category.assoc, h4]
      exact Over.w y
    · apply Over.OverMorphism.ext
      exact h4

variable {K : GroupScheme (Spec R)} {j : K ⟶ groupScheme F e} {I : Ideal B}
  (hI : ∀ (U : Over (Spec R)) (y : U ⟶ (groupScheme F e).X),
    y ∈ (SubgroupFunctor.range j).carrier U ↔
      ∀ b ∈ I, (e.homEquiv.symm (pointsEquiv F e U y)).hom b = 0)
include hI

theorem isAffineCutOutBy_range : IsAffineCutOutBy e (SubgroupFunctor.range j) I := by
  intro A f x
  rw [hI]
  refine forall₂_congr fun b _ => ?_
  rw [homEquiv_symm_pointsEquiv_apply, appTop_ΓSpecIso_inv]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1

theorem isCutOutBy_range : IsCutOutBy e (affineSubgroups (SubgroupFunctor.range j)) I :=
  isCutOutBy_affineSubgroups (isAffineCutOutBy_range hI)

theorem mem_range_iff_mem_affineSubgroups {U : Over (Spec R)} (y : U ⟶ (groupScheme F e).X) :
    y ∈ (SubgroupFunctor.range j).carrier U ↔
      pointsEquiv F e U y ∈ affineSubgroups (SubgroupFunctor.range j) ((algΓ R).obj U).unop := by
  rw [hI, isCutOutBy_range hI]

end Range

/-- The points over a test scheme `V` of a refined affine point are images of the algebra point
under the classifying map of the refinement. -/
theorem pointsEquiv_comp_affinePointsEquiv_symm {A : CommAlgCat.{u} R} {V : Over (Spec R)}
    (a : V ⟶ (algSpec R).obj (op A)) (g : F.obj A) :
    pointsEquiv F e V (a ≫ (affinePointsEquiv F e A).symm g) =
      F.map (((algΓAlgSpecAdjunction R).homEquiv V (op A)).symm a).unop g := by
  obtain ⟨φ, rfl⟩ := e.homEquiv.surjective g
  have hx : (affinePointsEquiv F e A).symm (e.homEquiv φ) = (algSpec R).map φ.op :=
    (affinePointsEquiv F e A).symm_apply_eq.2 (affinePointsEquiv_map F e A φ).symm
  rw [hx, pointsEquiv_apply]
  change e.homEquiv (((algΓAlgSpecAdjunction R).homEquiv V (op B)).symm
    (a ≫ (algSpec R).map φ.op)).unop = _
  rw [Adjunction.homEquiv_naturality_right_symm, unop_comp]
  exact e.homEquiv_comp _ _

theorem commute_mulEquiv_iff {M N : Type*} [Mul M] [Mul N] (σ : M ≃* N) {a b : M} :
    Commute (σ a) (σ b) ↔ Commute a b :=
  ⟨fun h => by simpa using h.map σ.symm.toMulHom, fun h => h.map σ.toMulHom⟩

section Normalizer

variable {K : GroupScheme (Spec R)} {j : K ⟶ groupScheme F e} {I : Ideal B}
  (hI : ∀ (U : Over (Spec R)) (y : U ⟶ (groupScheme F e).X),
    y ∈ (SubgroupFunctor.range j).carrier U ↔
      ∀ b ∈ I, (e.homEquiv.symm (pointsEquiv F e U y)).hom b = 0)
include hI

/-- Over the spectrum of an algebra, the normalizer of a closed subgroup is the algebra-level
normalizer family of its points. -/
theorem affineSubgroups_normalizer (A : CommAlgCat.{u} R) :
    affineSubgroups (SubgroupFunctor.range j).normalizer A =
      normalizerFamily (affineSubgroups (SubgroupFunctor.range j)) A := by
  ext g
  change (affinePointsEquiv F e A).symm g ∈ (SubgroupFunctor.range j).normalizer.carrier _ ↔ _
  constructor
  · intro hx A' f y hy
    have hy' : (affinePointsEquiv F e A').symm y ∈
        (SubgroupFunctor.range j).carrier ((algSpec R).obj (op A')) := hy
    have h := hx _ ((algSpec R).map f.op) _ hy'
    have hnat : (algSpec R).map f.op ≫ (affinePointsEquiv F e A).symm g =
        (affinePointsEquiv F e A').symm (F.map f g) := by
      rw [MulEquiv.eq_symm_apply, affinePointsEquiv_naturality, MulEquiv.apply_symm_apply]
    rw [hnat] at h
    constructor
    · change (affinePointsEquiv F e A').symm (F.map f g * y * (F.map f g)⁻¹) ∈
        (SubgroupFunctor.range j).carrier ((algSpec R).obj (op A'))
      simpa only [map_mul, map_inv] using h.1
    · change (affinePointsEquiv F e A').symm ((F.map f g)⁻¹ * y * F.map f g) ∈
        (SubgroupFunctor.range j).carrier ((algSpec R).obj (op A'))
      simpa only [map_mul, map_inv] using h.2
  · intro hg V a y hy
    rw [mem_range_iff_mem_affineSubgroups hI] at hy
    rw [mem_range_iff_mem_affineSubgroups hI, mem_range_iff_mem_affineSubgroups hI]
    simp only [map_mul, map_inv, pointsEquiv_comp_affinePointsEquiv_symm]
    exact hg _ _ _ hy

/-- Over the spectrum of an algebra, the centralizer of a closed subgroup is the algebra-level
centralizer family of its points. -/
theorem affineSubgroups_centralizer (A : CommAlgCat.{u} R) :
    affineSubgroups (SubgroupFunctor.range j).centralizer A =
      centralizerFamily (affineSubgroups (SubgroupFunctor.range j)) A := by
  ext g
  change (affinePointsEquiv F e A).symm g ∈ (SubgroupFunctor.range j).centralizer.carrier _ ↔ _
  constructor
  · intro hx A' f y hy
    have hy' : (affinePointsEquiv F e A').symm y ∈
        (SubgroupFunctor.range j).carrier ((algSpec R).obj (op A')) := hy
    have h := hx _ ((algSpec R).map f.op) _ hy'
    have hnat : (algSpec R).map f.op ≫ (affinePointsEquiv F e A).symm g =
        (affinePointsEquiv F e A').symm (F.map f g) := by
      rw [MulEquiv.eq_symm_apply, affinePointsEquiv_naturality, MulEquiv.apply_symm_apply]
    rw [hnat] at h
    exact (commute_mulEquiv_iff (affinePointsEquiv F e A').symm).1 h
  · intro hg V a y hy
    rw [mem_range_iff_mem_affineSubgroups hI] at hy
    rw [← commute_mulEquiv_iff (pointsEquiv F e V), pointsEquiv_comp_affinePointsEquiv_symm]
    exact hg _ _ _ hy

variable [Module.Projective R (B ⧸ I)]

/-- **The normalizer of a closed subgroup is cut out by `subgroupNormalizerIdeal`** on spectra of
algebras. -/
theorem isCutOutBy_affineSubgroups_normalizer :
    IsCutOutBy e (affineSubgroups (SubgroupFunctor.range j).normalizer) (subgroupNormalizerIdeal e I) :=
  fun A g => by
    rw [affineSubgroups_normalizer hI]
    exact isCutOutBy_normalizerFamily (isCutOutBy_range hI) A g

/-- **The centralizer of a closed subgroup is cut out by `subgroupCentralizerIdeal`** on spectra of
algebras. -/
theorem isCutOutBy_affineSubgroups_centralizer :
    IsCutOutBy e (affineSubgroups (SubgroupFunctor.range j).centralizer) (subgroupCentralizerIdeal e I) :=
  fun A g => by
    rw [affineSubgroups_centralizer hI]
    exact isCutOutBy_centralizerFamily (isCutOutBy_range hI) A g

/-- The normalizer of a closed subgroup is represented on every test scheme by the closed
subgroup scheme `Spec (B ⧸ subgroupNormalizerIdeal e I)`. -/
theorem isRepresentedBy_normalizer :
    (SubgroupFunctor.range j).normalizer.IsRepresentedBy
      (cutHom (isCutOutBy_affineSubgroups_normalizer hI)) :=
  isRepresentedBy_cutHom_affineSubgroups
    (isAffineCutOutBy_of_isCutOutBy (isCutOutBy_affineSubgroups_normalizer hI))

/-- The centralizer of a closed subgroup is represented on every test scheme by the closed
subgroup scheme `Spec (B ⧸ subgroupCentralizerIdeal e I)`. -/
theorem isRepresentedBy_centralizer :
    (SubgroupFunctor.range j).centralizer.IsRepresentedBy
      (cutHom (isCutOutBy_affineSubgroups_centralizer hI)) :=
  isRepresentedBy_cutHom_affineSubgroups
    (isAffineCutOutBy_of_isCutOutBy (isCutOutBy_affineSubgroups_centralizer hI))

end Normalizer

end Corepresented

namespace SubgroupFunctor

variable {S : Scheme.{u}} {H G G' : GroupScheme S}

/-- A homomorphism `f` maps the normalizer of `range i` into the normalizer of `range (i ≫ f)`. -/
theorem normalizer_range_le_comap (i : H ⟶ G) (f : G ⟶ G') :
    (range i).normalizer ≤ ((range (i ≫ f)).normalizer).comap f := by
  intro U x hx
  rw [mem_comap]
  intro V a y hy
  obtain ⟨t, rfl⟩ := mem_range.1 hy
  have hx' := hx V a (t ≫ i.hom.hom) (mem_range.2 ⟨t, rfl⟩)
  obtain ⟨t₁, h₁⟩ := mem_range.1 hx'.1
  obtain ⟨t₂, h₂⟩ := mem_range.1 hx'.2
  refine ⟨mem_range.2 ⟨t₁, ?_⟩, mem_range.2 ⟨t₂, ?_⟩⟩
  · rw [Grp.comp_hom_hom, ← Category.assoc, h₁]
    simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
  · rw [Grp.comp_hom_hom, ← Category.assoc, h₂]
    simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

/-- A homomorphism `f` maps the centralizer of `range i` into the centralizer of
`range (i ≫ f)`. -/
theorem centralizer_range_le_comap (i : H ⟶ G) (f : G ⟶ G') :
    (range i).centralizer ≤ ((range (i ≫ f)).centralizer).comap f := by
  intro U x hx
  rw [mem_comap]
  intro V a y hy
  obtain ⟨t, rfl⟩ := mem_range.1 hy
  have h := congrArg (· ≫ f.hom.hom) (hx V a (t ≫ i.hom.hom) (mem_range.2 ⟨t, rfl⟩)).eq
  simp only [MonObj.mul_comp, Category.assoc] at h
  show (a ≫ x ≫ f.hom.hom) * (t ≫ (i ≫ f).hom.hom) =
    (t ≫ (i ≫ f).hom.hom) * (a ≫ x ≫ f.hom.hom)
  rw [Grp.comp_hom_hom]
  exact h

theorem comp_hom_comp_inv_hom (e : G ≅ G') {T : Over S} (g : T ⟶ G.X) :
    (g ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = g := by
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]

/-- Normalizers of ranges are transported along isomorphisms of the ambient group. -/
theorem normalizer_range_eq_comap_of_iso (i : H ⟶ G) (e : G ≅ G') :
    (range i).normalizer = ((range (i ≫ e.hom)).normalizer).comap e.hom := by
  refine le_antisymm (normalizer_range_le_comap i e.hom) fun T g hg => ?_
  have h : (g ≫ e.hom.hom.hom) ≫ e.inv.hom.hom ∈
      (range ((i ≫ e.hom) ≫ e.inv)).normalizer.carrier T :=
    normalizer_range_le_comap (i ≫ e.hom) e.inv T hg
  rwa [Category.assoc, Iso.hom_inv_id, Category.comp_id, comp_hom_comp_inv_hom] at h

/-- Centralizers of ranges are transported along isomorphisms of the ambient group. -/
theorem centralizer_range_eq_comap_of_iso (i : H ⟶ G) (e : G ≅ G') :
    (range i).centralizer = ((range (i ≫ e.hom)).centralizer).comap e.hom := by
  refine le_antisymm (centralizer_range_le_comap i e.hom) fun T g hg => ?_
  have h : (g ≫ e.hom.hom.hom) ≫ e.inv.hom.hom ∈
      (range ((i ≫ e.hom) ≫ e.inv)).centralizer.carrier T :=
    centralizer_range_le_comap (i ≫ e.hom) e.inv T hg
  rwa [Category.assoc, Iso.hom_inv_id, Category.comp_id, comp_hom_comp_inv_hom] at h

end SubgroupFunctor

namespace AffineCoordinates

open Corepresented

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  {H : GroupScheme (Spec R)} (i : H ⟶ G)

/-- The closed subgroup `i` in the chosen corepresented coordinates of `G`. -/
abbrev coordinateHom : H ⟶ Corepresented.groupScheme (functor G) (corepresentation G) :=
  i ≫ (groupSchemeIso G).inv

instance [hi : IsClosedImmersion i.hom.hom.left] :
    IsClosedImmersion (coordinateHom i).hom.hom.left := by
  have : IsClosedImmersion (groupSchemeIso G).inv.hom.hom.left :=
    IsClosedSubgroup.of_iso (groupSchemeIso G).symm
  change IsClosedImmersion (i.hom.hom.left ≫ (groupSchemeIso G).inv.hom.hom.left)
  infer_instance

variable {i} {I : Ideal (algebra G)}
  (hI : ∀ (U : Over (Spec R)) (y : U ⟶ (Corepresented.groupScheme (functor G)
      (corepresentation G)).X),
    y ∈ (SubgroupFunctor.range (coordinateHom i)).carrier U ↔
      ∀ b ∈ I, ((corepresentation G).homEquiv.symm (pointsEquiv (functor G)
        (corepresentation G) U y)).hom b = 0)
  [Module.Projective R (algebra G ⧸ I)]
include hI

/-- **Representability of the normalizer of a closed subgroup of an affine group**, on every
test scheme, by an explicit closed subgroup scheme cut out by `subgroupNormalizerIdeal`. -/
theorem isRepresentedBy_normalizer_range :
    (SubgroupFunctor.range i).normalizer.IsRepresentedBy
      (cutHom (isCutOutBy_affineSubgroups_normalizer hI) ≫ (groupSchemeIso G).hom) := by
  rw [SubgroupFunctor.normalizer_range_eq_comap_of_iso i (groupSchemeIso G).symm]
  exact (isRepresentedBy_normalizer hI).comp_iso (groupSchemeIso G)

/-- **Representability of the centralizer of a closed subgroup of an affine group**, on every
test scheme, by an explicit closed subgroup scheme cut out by `subgroupCentralizerIdeal`. -/
theorem isRepresentedBy_centralizer_range :
    (SubgroupFunctor.range i).centralizer.IsRepresentedBy
      (cutHom (isCutOutBy_affineSubgroups_centralizer hI) ≫ (groupSchemeIso G).hom) := by
  rw [SubgroupFunctor.centralizer_range_eq_comap_of_iso i (groupSchemeIso G).symm]
  exact (isRepresentedBy_centralizer hI).comp_iso (groupSchemeIso G)

theorem isClosedSubgroup_normalizer_range :
    IsClosedSubgroup (cutHom (isCutOutBy_affineSubgroups_normalizer hI) ≫
      (groupSchemeIso G).hom) := by
  have : IsClosedImmersion (groupSchemeIso G).hom.hom.hom.left :=
    IsClosedSubgroup.of_iso (groupSchemeIso G)
  change IsClosedImmersion ((cutHom _).hom.hom.left ≫ (groupSchemeIso G).hom.hom.hom.left)
  infer_instance

theorem isClosedSubgroup_centralizer_range :
    IsClosedSubgroup (cutHom (isCutOutBy_affineSubgroups_centralizer hI) ≫
      (groupSchemeIso G).hom) := by
  have : IsClosedImmersion (groupSchemeIso G).hom.hom.hom.left :=
    IsClosedSubgroup.of_iso (groupSchemeIso G)
  change IsClosedImmersion ((cutHom _).hom.hom.left ≫ (groupSchemeIso G).hom.hom.hom.left)
  infer_instance

end AffineCoordinates

/-- **Normalizers and centralizers of closed subgroups over a field are closed** (Milne,
Propositions 1.83 and 1.92, for affine groups). For a closed subgroup `i` of an affine group
scheme over a field, the all-test normalizer and centralizer of its points have closed
representatives. -/
theorem hasClosedRepresentative_normalizer_centralizer_range {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left] (i : H ⟶ G)
    (hi : IsClosedSubgroup i) :
    (SubgroupFunctor.range i).normalizer.HasClosedRepresentative ∧
      (SubgroupFunctor.range i).centralizer.HasClosedRepresentative := by
  have : IsClosedImmersion i.hom.hom.left := hi
  obtain ⟨I, hI⟩ := Corepresented.exists_ideal_range (AffineCoordinates.coordinateHom i)
  exact ⟨⟨_, _, AffineCoordinates.isClosedSubgroup_normalizer_range hI,
      AffineCoordinates.isRepresentedBy_normalizer_range hI⟩,
    ⟨_, _, AffineCoordinates.isClosedSubgroup_centralizer_range hI,
      AffineCoordinates.isRepresentedBy_centralizer_range hI⟩⟩

end Langlands.GroupScheme
