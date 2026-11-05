import Langlands.Algebra.TensorEmbeddingDescent
import Langlands.AlgebraicGeometry.AffineCoordinateBaseChange
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionCounit
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Affine morphism descent detected by an embedding -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AffineEmbeddingDescent

variable {k : Type u} [Field k]
    {K : Type u} [CommRing K] [Nontrivial K] [Algebra k K]
    {A B C : CommAlgCat.{u} (CommRingCat.of k)}

/-- A map between affine spectra descends if its composite with an
embedding of coordinate algebras descends. -/
theorem existsUnique_specHom
    (f : A ⟶ B) (hf : Function.Injective f.hom)
    (g : (algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of k (K ⊗[k] A))) ⟶
      (algSpec (CommRingCat.of k)).obj (op C))
    (h : (algSpec (CommRingCat.of k)).obj (op B) ⟶
      (algSpec (CommRingCat.of k)).obj (op C))
    (hgh : (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id k K) f.hom)).op ≫ g =
      (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom
          (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B)).op ≫ h) :
    ∃! g₀ : (algSpec (CommRingCat.of k)).obj (op A) ⟶
        (algSpec (CommRingCat.of k)).obj (op C),
      (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom
          (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)).op ≫ g₀ = g := by
  let F := algSpec (CommRingCat.of k)
  let FF : F.FullyFaithful := algSpec.fullyFaithful
  let g' := (FF.preimage g).unop.hom
  let h' := (FF.preimage h).unop.hom
  have hgh' : (Algebra.TensorProduct.map (AlgHom.id k K) f.hom).comp g' =
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).comp h' := by
    have hg : F.map (CommAlgCat.ofHom g').op = g := FF.map_preimage g
    have hh : F.map (CommAlgCat.ofHom h').op = h := FF.map_preimage h
    rw [← hg, ← hh, ← F.map_comp, ← F.map_comp] at hgh
    exact congrArg (fun q => q.unop.hom) (FF.map_injective hgh)
  obtain ⟨g₀, hg₀, huniq⟩ :=
    TensorEmbeddingDescent.existsUnique_algHom_of_map_eq f.hom hf g' h' hgh'
  refine ⟨F.map (CommAlgCat.ofHom g₀).op, ?_, ?_⟩
  · change F.map _ ≫ F.map _ = g
    rw [← F.map_comp]
    change F.map (CommAlgCat.ofHom
      ((Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).comp g₀)).op = g
    rw [hg₀]
    exact FF.map_preimage g
  · intro g₁ hg₁
    let g₁' := (FF.preimage g₁).unop.hom
    have hg₁' : (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).comp g₁' =
        g' := by
      have hmap : F.map (CommAlgCat.ofHom g₁').op = g₁ := FF.map_preimage g₁
      have hg : F.map (CommAlgCat.ofHom g').op = g := FF.map_preimage g
      rw [← hmap, ← hg, ← F.map_comp] at hg₁
      exact congrArg (fun q => q.unop.hom) (FF.map_injective hg₁)
    have he := huniq g₁' hg₁'
    rw [← FF.map_preimage g₁]
    change F.map (CommAlgCat.ofHom g₁').op = _
    rw [he]

open PointTopology

/-- Actual scalar extension, regarded again as a scheme over the original field. -/
def scalarExtension (k K : Type u) [CommRing k] [CommRing K] [Algebra k K] :
    Over (Spec (CommRingCat.of k)) ⥤ Over (Spec (CommRingCat.of k)) :=
  Over.pullback (Spec.algebraMap k K) ⋙ Over.map (Spec.algebraMap k K)

/-- The canonical projection from the actual scalar extension. -/
def projection (X : Over (Spec (CommRingCat.of k))) :
    (scalarExtension k K).obj X ⟶ X :=
  Over.homMk (pullback.fst X.hom (Spec.algebraMap k K)) pullback.condition

omit [Nontrivial K] in
@[reassoc]
theorem projection_natural {X Y : Over (Spec (CommRingCat.of k))} (p : X ⟶ Y) :
    (scalarExtension k K).map p ≫ projection Y = projection X ≫ p := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- The tensor spectrum comparison, with scalars restricted to the original field. -/
def tensorModelIso (A : CommAlgCat.{u} (CommRingCat.of k)) :
    (scalarExtension k K).obj ((algSpec (CommRingCat.of k)).obj (op A)) ≅
      (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k (K ⊗[k] A))) :=
  (Over.map (Spec.algebraMap k K)).mapIso
      (AffineCoordinateBaseChange.tensorSpecIso (CommAlgCat.of k K) A) ≪≫
    ringTestRestrictScalarsIso k K (K ⊗[k] A)

omit [Nontrivial K] in
/-- Naturality of the tensor comparison for actual scalar extension. -/
theorem tensorModelIso_natural (f : A ⟶ B) :
    (scalarExtension k K).map ((algSpec (CommRingCat.of k)).map f.op) ≫
        (tensorModelIso (K := K) A).hom =
      (tensorModelIso (K := K) B).hom ≫
        (algSpec (CommRingCat.of k)).map
          (CommAlgCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id k K) f.hom)).op := by
  apply Over.OverMorphism.ext
  simp only [tensorModelIso, Iso.trans_hom, Over.comp_left,
    Functor.mapIso_hom, Over.map_map_left, ringTestRestrictScalarsIso_hom_left,
    Category.comp_id]
  have h := congrArg (fun q => q.left)
    (ringBaseChangeSpectrumIso_natural (CommRingCat.of k) (CommAlgCat.of k K) f.hom)
  convert h using 1 <;> rfl

omit [Nontrivial K] in
/-- The projection corresponds to inclusion of the original coordinate algebra. -/
@[reassoc]
theorem tensorModelIso_inv_projection (A : CommAlgCat.{u} (CommRingCat.of k)) :
    (tensorModelIso (K := K) A).inv ≫ projection
        ((algSpec (CommRingCat.of k)).obj (op A)) =
      (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom
          (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)).op := by
  apply Over.OverMorphism.ext
  change (𝟙 _ ≫
      (AffineCoordinateBaseChange.tensorSpecIso (CommAlgCat.of k K) A).inv.left) ≫
        pullback.fst _ _ = _
  rw [Category.id_comp]
  exact ringBaseChangeSpectrumIso_inv_fst (CommRingCat.of k) (CommAlgCat.of k K) A

variable {X T Y : Over (Spec (CommRingCat.of k))}
    [IsAffine X.left] [IsAffine T.left] [IsAffine Y.left]

/-- The actual affine scheme presented by its coordinate algebra. -/
def affineSpectrumIso (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] :
    X ≅ (algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of k (AffineCoordinateRing k X))) :=
  affineSchemeOverIso k X

/-- Naturality of the canonical affine coordinate presentation. -/
theorem affineSpectrumIso_natural (p : T ⟶ X) :
    p ≫ (affineSpectrumIso X).hom =
      (affineSpectrumIso T).hom ≫
        (algSpec (CommRingCat.of k)).map
          (CommAlgCat.ofHom (affineCoordinatePullback k p)).op := by
  apply Over.OverMorphism.ext
  exact (Scheme.isoSpec_hom_naturality p.left).symm

/-- Scheme-theoretic dominance makes the actual coordinate pullback injective. -/
theorem affineCoordinatePullback_injective (p : T ⟶ X)
    [IsSchemeTheoreticallyDominant p.left] [QuasiCompact p.left] :
    Function.Injective (affineCoordinatePullback k p) := by
  have hp := p.left.app_injective ⊤
  change Function.Injective p.left.appTop.hom
  exact hp

/-- The tensor-coordinate model of the actual scalar extension of an affine scheme. -/
def affineModelIso (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] :
    (scalarExtension k K).obj X ≅
      (algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of k (K ⊗[k] AffineCoordinateRing k X))) :=
  (scalarExtension k K).mapIso (affineSpectrumIso X) ≪≫
    tensorModelIso (CommAlgCat.of k (AffineCoordinateRing k X))

omit [Nontrivial K] in
/-- Naturality of the actual affine scalar-extension presentation. -/
theorem affineModelIso_natural (p : T ⟶ X) :
    (scalarExtension k K).map p ≫ (affineModelIso (K := K) X).hom =
      (affineModelIso (K := K) T).hom ≫
        (algSpec (CommRingCat.of k)).map
          (CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k K)
            (affineCoordinatePullback k p))).op := by
  simp only [affineModelIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, affineSpectrumIso_natural,
    Functor.map_comp, Category.assoc, tensorModelIso_natural]
  simp only [Category.assoc]
  rfl

omit [Nontrivial K] in
/-- The inverse tensor presentation recovers the actual projection. -/
@[reassoc]
theorem affineModelIso_inv_projection (X : Over (Spec (CommRingCat.of k)))
    [IsAffine X.left] :
    (affineModelIso (K := K) X).inv ≫ projection X =
      (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight :
          AffineCoordinateRing k X →ₐ[k] K ⊗[k] AffineCoordinateRing k X)).op ≫
        (affineSpectrumIso X).inv := by
  simp only [affineModelIso, Iso.trans_inv, Functor.mapIso_inv]
  rw [Category.assoc, projection_natural, ← Category.assoc,
    tensorModelIso_inv_projection]

set_option maxHeartbeats 800000 in
/-- A morphism from the scalar extension of an affine scheme descends uniquely
if its composite with a schematically dominant affine parametrization descends. -/
theorem existsUnique_hom (p : T ⟶ X)
    [IsSchemeTheoreticallyDominant p.left] [QuasiCompact p.left]
    (g : (scalarExtension k K).obj X ⟶ Y) (h : T ⟶ Y)
    (hgh : (scalarExtension k K).map p ≫ g = projection T ≫ h) :
    ∃! g₀ : X ⟶ Y, projection X ≫ g₀ = g := by
  let f : CommAlgCat.of k (AffineCoordinateRing k X) ⟶
      CommAlgCat.of k (AffineCoordinateRing k T) :=
    CommAlgCat.ofHom (affineCoordinatePullback k p)
  let eX := affineSpectrumIso X
  let eT := affineSpectrumIso T
  let eY := affineSpectrumIso Y
  let dX := affineModelIso (K := K) X
  let dT := affineModelIso (K := K) T
  have hn : (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k K) f.hom)).op ≫
        dX.inv = dT.inv ≫ (scalarExtension k K).map p := by
    apply (cancel_epi dT.hom).mp
    have hp := affineModelIso_natural (K := K) p
    change (scalarExtension k K).map p ≫ dX.hom =
      dT.hom ≫ (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k K) f.hom)).op at hp
    rw [← Category.assoc, ← hp, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  have heq : (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k K) f.hom)).op ≫
        (dX.inv ≫ g ≫ eY.hom) =
      (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight :
          AffineCoordinateRing k T →ₐ[k] K ⊗[k] AffineCoordinateRing k T)).op ≫
        (eT.inv ≫ h ≫ eY.hom) := by
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← Category.assoc ((scalarExtension k K).map p), hgh]
    simp only [Category.assoc]
    rw [← Category.assoc dT.inv (projection T), affineModelIso_inv_projection]
    simp only [eT, Category.assoc]
  obtain ⟨g₀, hg₀, hu⟩ := existsUnique_specHom f
    (affineCoordinatePullback_injective p)
    (dX.inv ≫ g ≫ eY.hom) (eT.inv ≫ h ≫ eY.hom) heq
  refine ⟨eX.hom ≫ g₀ ≫ eY.inv, ?_, ?_⟩
  · apply (cancel_epi dX.inv).mp
    rw [← Category.assoc, affineModelIso_inv_projection]
    simp only [eX, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hg₀]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro g₁ hg₁
    have hg₁' : (algSpec (CommRingCat.of k)).map
          (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight :
            AffineCoordinateRing k X →ₐ[k] K ⊗[k] AffineCoordinateRing k X)).op ≫
          (eX.inv ≫ g₁ ≫ eY.hom) = dX.inv ≫ g ≫ eY.hom := by
      rw [← Category.assoc, ← affineModelIso_inv_projection]
      change (dX.inv ≫ projection X) ≫ (g₁ ≫ eY.hom) = _
      rw [Category.assoc, ← Category.assoc (projection X), hg₁]
    have he := hu (eX.inv ≫ g₁ ≫ eY.hom) hg₁'
    calc
      g₁ = eX.hom ≫ (eX.inv ≫ g₁ ≫ eY.hom) ≫ eY.inv := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
          Category.comp_id]
      _ = eX.hom ≫ g₀ ≫ eY.inv := by rw [he]

/-- The actual descended morphism furnished by dominant affine descent. -/
def descendHom (p : T ⟶ X)
    [IsSchemeTheoreticallyDominant p.left] [QuasiCompact p.left]
    (g : (scalarExtension k K).obj X ⟶ Y) (h : T ⟶ Y)
    (hgh : (scalarExtension k K).map p ≫ g = projection T ≫ h) : X ⟶ Y :=
  (existsUnique_hom p g h hgh).choose

/-- Pulling the descended morphism back along the actual projection recovers
its given scalar-extension morphism. -/
@[reassoc]
theorem projection_comp_descendHom (p : T ⟶ X)
    [IsSchemeTheoreticallyDominant p.left] [QuasiCompact p.left]
    (g : (scalarExtension k K).obj X ⟶ Y) (h : T ⟶ Y)
    (hgh : (scalarExtension k K).map p ≫ g = projection T ≫ h) :
    projection X ≫ descendHom p g h hgh = g :=
  (existsUnique_hom p g h hgh).choose_spec.1

/-- Recovery along the projection uniquely characterizes the descended map. -/
theorem descendHom_unique (p : T ⟶ X)
    [IsSchemeTheoreticallyDominant p.left] [QuasiCompact p.left]
    (g : (scalarExtension k K).obj X ⟶ Y) (h : T ⟶ Y)
    (hgh : (scalarExtension k K).map p ≫ g = projection T ≫ h)
    (g₀ : X ⟶ Y) (hg₀ : projection X ≫ g₀ = g) :
    g₀ = descendHom p g h hgh :=
  (existsUnique_hom p g h hgh).choose_spec.2 g₀ hg₀

end Langlands.AlgebraicGeometry.AffineEmbeddingDescent
