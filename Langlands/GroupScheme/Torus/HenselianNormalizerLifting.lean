import Langlands.GroupScheme.Torus.IdentityTransporterEtaleLift
import Langlands.GroupScheme.Torus.ExponentHomomorphisms
import Langlands.GroupScheme.IntegralModel.SplitIntegralPoints
import Langlands.CommutativeAlgebra.HenselianSections

/-! # Exact Henselian lifting of split-torus transporters and normalizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace PointwiseSchemeAction

variable {R k : Type u} [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]
    {L : Type u} [AddCommGroup L]
    (i₁ i₂ : (Diagonalizable.groupScheme (CommRingCat.of R) L).toGrp ⟶ G)

/-- A prescribed residue transporter between diagonalizable homomorphisms
lifts to an integral transporter, with exact recovery of that point. -/
theorem exists_henselian_transporter
    (hG : Smooth G.X.hom) (hk : Function.Surjective (algebraMap R k))
    (g₀ : Over.mk (Spec.algebraMap R k) ⟶ G.X)
    (hg₀ : IsTransporter i₁ i₂ g₀) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      IsTransporter i₁ i₂ g ∧
        (Over.homMk (Spec.algebraMap R k) (by simp) :
          Over.mk (Spec.algebraMap R k) ⟶ Over.mk (𝟙 _)) ≫ g = g₀ := by
  let C : CommAlgCat.{u} (CommRingCat.of R) := CommAlgCat.of R k
  obtain ⟨y, hy⟩ := (exists_relativeTransporter_factor_iff i₁ i₂
    (C := C) g₀).mpr hg₀
  let : Smooth (relativeTransporterScheme i₁ i₂).hom :=
    smooth_relativeTransporterScheme i₁ i₂ hG
  obtain ⟨s, hs, hsk⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
      hk (relativeTransporterScheme i₁ i₂).hom y.left (Over.w y)
  let a : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      relativeTransporterScheme i₁ i₂ := Over.homMk s hs
  refine ⟨a ≫ relativeTransporterHom i₁ i₂,
    (relativeTransporterHom_isTransporter i₁ i₂).restrict a, ?_⟩
  apply Over.OverMorphism.ext
  change (Spec.algebraMap R k ≫ s) ≫ (relativeTransporterHom i₁ i₂).left = g₀.left
  rw [hsk]
  exact congrArg Over.Hom.left hy

variable {H : GroupScheme (Spec (CommRingCat.of R))}

/-- The exact transporter lift is unchanged by identifying the source with
an actual diagonalizable group. -/
theorem exists_henselian_transporter_of_sourceIso
    (j₁ j₂ : H ⟶ G)
    (e : (Diagonalizable.groupScheme (CommRingCat.of R) L).toGrp ≅ H)
    (hG : Smooth G.X.hom) (hk : Function.Surjective (algebraMap R k))
    (g₀ : Over.mk (Spec.algebraMap R k) ⟶ G.X)
    (hg₀ : IsTransporter j₁ j₂ g₀) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      IsTransporter j₁ j₂ g ∧
        (Over.homMk (Spec.algebraMap R k) (by simp) :
          Over.mk (Spec.algebraMap R k) ⟶ Over.mk (𝟙 _)) ≫ g = g₀ := by
  obtain ⟨g, hg, hrec⟩ := exists_henselian_transporter
    (e.hom ≫ j₁) (e.hom ≫ j₂) hG hk g₀ (hg₀.precomp e.hom)
  refine ⟨g, ?_, hrec⟩
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using hg.precomp e.inv

/-- A specified residue transporter between maps from a split torus lifts
over the original Henselian ring. -/
theorem exists_henselian_transporter_of_split
    (j₁ j₂ : H ⟶ G) (hH : IsSplitTorus H)
    (hG : Smooth G.X.hom) (hk : Function.Surjective (algebraMap R k))
    (g₀ : Over.mk (Spec.algebraMap R k) ⟶ G.X)
    (hg₀ : IsTransporter j₁ j₂ g₀) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      IsTransporter j₁ j₂ g ∧
        (Over.homMk (Spec.algebraMap R k) (by simp) :
          Over.mk (Spec.algebraMap R k) ⟶ Over.mk (𝟙 _)) ≫ g = g₀ := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hH
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  exact exists_henselian_transporter_of_sourceIso j₁ j₂
    (Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (I → ℤ)) ≪≫ e.symm)
    hG hk g₀ hg₀

end PointwiseSchemeAction

section SplitAutomorphisms

variable {S : Scheme.{u}} {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) {T : CommGroupScheme S}

/-- Every automorphism of a field fibre of a split torus extends over its
original base, recovering the specified actual automorphism. -/
theorem IsSplitTorus.automorphism_fieldBaseChange_surjective
    (hT : IsSplitTorus T.toGrp) :
    Function.Surjective
      (fun σ : T ≅ T => (CommGroupScheme.baseChange b).mapIso σ) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := hI
  let := Fintype.ofFinite I
  let eC : T ≅ splitTorus.commGroupScheme S I := CommGroupScheme.isoOfGroupIso e
  let B := CommGroupScheme.baseChange b
  let d := splitTorus.commBaseChangeIso b I
  let q := B.mapIso eC ≪≫ d
  intro σ'
  let c := q.symm ≪≫ σ' ≪≫ q
  let cG : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) I :=
    { hom := CommGroupScheme.groupHom c.hom
      inv := CommGroupScheme.groupHom c.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom c.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom c.inv_hom_id }
  let c₀ : splitTorus.commGroupScheme S I ≅ splitTorus.commGroupScheme S I :=
    CommGroupScheme.isoOfGroupIso (splitTorus.fieldAutomorphismExtension k I S cG)
  refine ⟨eC ≪≫ c₀ ≪≫ eC.symm, ?_⟩
  apply Iso.ext
  change B.map (eC.hom ≫ c₀.hom ≫ eC.inv) = σ'.hom
  have hc : d.inv ≫ B.map c₀.hom ≫ d.hom = c.hom :=
    congrArg Additive.ofMul (splitTorus.fieldAutomorphismExtension_baseChange k I S cG b)
  have hc' : B.map c₀.hom = d.hom ≫ c.hom ≫ d.inv := by
    rw [← hc]
    simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Functor.map_comp, Functor.map_comp, hc']
  dsimp only [c, q, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [B.map_id, Category.id_comp, ← B.map_comp, eC.hom_inv_id,
    B.map_id, Category.comp_id]

end SplitAutomorphisms

section Normalizing

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    {i : T.toGrp ⟶ G} {n : Over.mk (𝟙 S) ⟶ G.X} {σ : T ≅ T}

/-- The all-test transporter equation recovers the specified normalizing
automorphism as an equality of actual group-scheme homomorphisms. -/
theorem isNormalizingPoint_of_isTransporter
    (hn : PointwiseSchemeAction.IsTransporter (CommGroupScheme.groupHom σ.hom ≫ i) i n) :
    IsNormalizingPoint i n σ := by
  apply hom_ext_points
  intro V t
  rw [Grp.comp_hom_hom, ← Category.assoc, G.comp_innerIso_hom]
  have h := hn V (Over.homMk V.hom (by simp)) t
  change (t ≫ (CommGroupScheme.groupHom σ.hom ≫ i).hom.hom) * G.constantPoint n V =
    G.constantPoint n V * (t ≫ i.hom.hom) at h
  exact (mul_inv_eq_iff_eq_mul.mpr h.symm)

end Normalizing

section HenselianNormalizers

variable {R k : Type u} [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k]
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hG : Smooth G.X.hom) (hk : Function.Surjective (algebraMap R k))

include hT hG hk in
/-- A residue normalizer with an integrally specified torus action lifts
with that action and with exact recovery of its residue point. -/
theorem exists_henselian_normalizer_of_automorphism
    (σ : T ≅ T)
    (n₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      ((baseChange (Spec.algebraMap R k)).obj G).X)
    (hn₀ : IsNormalizingPoint ((baseChange (Spec.algebraMap R k)).map i) n₀
      ((CommGroupScheme.baseChange (Spec.algebraMap R k)).mapIso σ)) :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      IsNormalizingPoint i n σ ∧
        baseChangeSectionHom (Spec.algebraMap R k) G n = n₀ := by
  let b := Spec.algebraMap R k
  have ht : PointwiseSchemeAction.IsTransporter
      ((baseChange b).map (CommGroupScheme.groupHom σ.hom ≫ i))
      ((baseChange b).map i) n₀ := by
    rw [Functor.map_comp]
    exact hn₀.isTransporter
  let c : Over.mk b ⟶ (Over.map b).obj (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    Over.homMk (𝟙 _) (by simp)
  obtain ⟨n, hn, hrec⟩ :=
    PointwiseSchemeAction.exists_henselian_transporter_of_split
      (CommGroupScheme.groupHom σ.hom ≫ i) i hT hG hk
      (c ≫ baseChangePointsEquiv b G _ n₀)
      ((ht.baseChangePointsEquiv b).restrict c)
  refine ⟨n, isNormalizingPoint_of_isTransporter hn, ?_⟩
  apply (baseChangePointsEquiv b G _).injective
  rw [baseChangePointsEquiv_baseChangeSectionHom]
  apply Over.OverMorphism.ext
  have hh := congrArg Over.Hom.left hrec
  change b ≫ n.left = (𝟙 (Spec (CommRingCat.of k))) ≫
    n₀.left ≫ Limits.pullback.fst G.X.hom b at hh
  change b ≫ n.left = n₀.left ≫ Limits.pullback.fst G.X.hom b
  simpa only [Category.id_comp] using hh

include hT hG hk in
/-- Every residue normalizer of a split integral torus lifts over a Henselian
local ring, preserving both its point and its specified torus automorphism. -/
theorem exists_henselian_normalizer
    (n₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      ((baseChange (Spec.algebraMap R k)).obj G).X)
    (σ₀ : (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T ≅
      (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T)
    (hn₀ : IsNormalizingPoint ((baseChange (Spec.algebraMap R k)).map i) n₀ σ₀) :
    ∃ (n : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X) (σ : T ≅ T),
      IsNormalizingPoint i n σ ∧
        baseChangeSectionHom (Spec.algebraMap R k) G n = n₀ ∧
        (CommGroupScheme.baseChange (Spec.algebraMap R k)).mapIso σ = σ₀ := by
  obtain ⟨σ, hσ⟩ := hT.automorphism_fieldBaseChange_surjective (Spec.algebraMap R k) σ₀
  obtain ⟨n, hn, hrec⟩ := exists_henselian_normalizer_of_automorphism i hT hG hk σ n₀
    ((congrArg (fun τ => IsNormalizingPoint
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T)
      ((baseChange (Spec.algebraMap R k)).map i) n₀ τ) hσ).mpr hn₀)
  exact ⟨n, σ, hn, hrec, hσ⟩

/-- A chosen integral lift of a prescribed residue normalizer point and torus
    automorphism, together with the normalizer and exact recovery equations. -/
def henselianNormalizerLift
    (n₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      ((baseChange (Spec.algebraMap R k)).obj G).X)
    (σ₀ : (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T ≅
      (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T)
    (hn₀ : IsNormalizingPoint ((baseChange (Spec.algebraMap R k)).map i) n₀ σ₀) :
    { p : (Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X) × (T ≅ T) //
      IsNormalizingPoint i p.1 p.2 ∧
        baseChangeSectionHom (Spec.algebraMap R k) G p.1 = n₀ ∧
        (CommGroupScheme.baseChange (Spec.algebraMap R k)).mapIso p.2 = σ₀ } :=
  Classical.indefiniteDescription _ (by
    obtain ⟨n, σ, hn⟩ := exists_henselian_normalizer i hT hG hk n₀ σ₀ hn₀
    exact ⟨(n, σ), hn⟩)

end HenselianNormalizers

end Langlands.GroupScheme
