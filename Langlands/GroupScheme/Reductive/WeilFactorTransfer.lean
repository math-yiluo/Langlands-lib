import Langlands.GroupScheme.Reductive.WeilFactorProjection
import Langlands.GroupScheme.Reductive.WeilFactorIdempotentRigidityStatement

/-! # Transfer of idempotents along an isomorphism of Weil restrictions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilFactor

variable {A B B'' : Type u} [CommRing A] [CommRing B] [CommRing B''] [Algebra A B]
  [Algebra A B''] [Module.Finite A B] [Module.Projective A B] [Module.Finite A B'']
  [Module.Projective A B'']
  {G : GroupScheme (Spec (CommRingCat.of B))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {G'' : GroupScheme (Spec (CommRingCat.of B''))} [IsAffine G''.X.left]
  [LocallyOfFiniteType G''.X.hom]

/-- A homomorphism of Weil restrictions acting on the group functors over `T`. -/
def transportNat (f : AffineWeil.groupScheme A B G ⟶ AffineWeil.groupScheme A B'' G'')
    (T : CommAlgCat.{u} (CommRingCat.of A)) : Fun A B G T ⟶ Fun A B'' G'' T where
  app X := GrpCat.ofHom ((AffineWeil.groupScheme A B G).affinePointsTarget f X.right)
  naturality X Y a := by
    refine GrpCat.ext ?_
    intro x
    exact (DFunLike.congr_fun
      ((AffineWeil.groupScheme A B G).affinePointsTarget_naturality f a.right) x).symm

/-- Conjugation of a transformation by an isomorphism of Weil restrictions. -/
def conj (Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'')
    {T : CommAlgCat.{u} (CommRingCat.of A)} (ψ : Fun A B G T ⟶ Fun A B G T) :
    Fun A B'' G'' T ⟶ Fun A B'' G'' T :=
  transportNat Φ.inv T ≫ ψ ≫ transportNat Φ.hom T

variable (Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'')
  {T : CommAlgCat.{u} (CommRingCat.of A)}

theorem transportNat_inv_hom :
    transportNat Φ.inv T ≫ transportNat Φ.hom T = 𝟙 _ := by
  refine ext_pt fun X x => ?_
  have h : Φ.inv.hom.hom ≫ Φ.hom.hom.hom = 𝟙 _ := congrArg (fun f => f.hom.hom) Φ.inv_hom_id
  change (x ≫ Φ.inv.hom.hom) ≫ Φ.hom.hom.hom = x
  rw [Category.assoc, h, Category.comp_id]

theorem transportNat_hom_inv :
    transportNat Φ.hom T ≫ transportNat Φ.inv T = 𝟙 _ := by
  refine ext_pt fun X x => ?_
  have h : Φ.hom.hom.hom ≫ Φ.inv.hom.hom = 𝟙 _ := congrArg (fun f => f.hom.hom) Φ.hom_inv_id
  change (x ≫ Φ.hom.hom.hom) ≫ Φ.inv.hom.hom = x
  rw [Category.assoc, h, Category.comp_id]

theorem conj_comp (ψ ψ' : Fun A B G T ⟶ Fun A B G T) :
    conj Φ (ψ ≫ ψ') = conj Φ ψ ≫ conj Φ ψ' := by
  simp only [conj, Category.assoc]
  rw [reassoc_of% (transportNat_hom_inv Φ (T := T))]

theorem conj_idem {ψ : Fun A B G T ⟶ Fun A B G T} (hψ : ψ ≫ ψ = ψ) :
    conj Φ ψ ≫ conj Φ ψ = conj Φ ψ := by
  rw [← conj_comp, hψ]

theorem pt_conj (ψ : Fun A B G T ⟶ Fun A B G T) (X : Under T)
    (x : (AffineWeil.groupScheme A B'' G'').affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)) :
    pt (conj Φ ψ) X x =
      (AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _
        (pt ψ X ((AffineWeil.groupScheme A B'' G'').affinePointsTarget Φ.inv _ x)) := rfl

theorem conj_normal {ψ : Fun A B G T ⟶ Fun A B G T}
    (hψ : ∀ (X : Under T) (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt ψ X (h * x * h⁻¹) = h * pt ψ X x * h⁻¹)
    (X : Under T) (h x : (AffineWeil.groupScheme A B'' G'').affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)) :
    pt (conj Φ ψ) X (h * x * h⁻¹) = h * pt (conj Φ ψ) X x * h⁻¹ := by
  have hid : ∀ y : (AffineWeil.groupScheme A B'' G'').affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right),
      (AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _
        ((AffineWeil.groupScheme A B'' G'').affinePointsTarget Φ.inv _ y) = y := fun y =>
    congrArg (fun ν => pt ν X y) (transportNat_inv_hom Φ (T := T))
  rw [pt_conj, pt_conj,
    map_mul ((AffineWeil.groupScheme A B'' G'').affinePointsTarget Φ.inv _),
    map_mul ((AffineWeil.groupScheme A B'' G'').affinePointsTarget Φ.inv _),
    map_inv ((AffineWeil.groupScheme A B'' G'').affinePointsTarget Φ.inv _), hψ,
    map_mul ((AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _),
    map_mul ((AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _),
    map_inv ((AffineWeil.groupScheme A B G).affinePointsTarget Φ.hom _), hid]

theorem pt_conj_eq_one {ψ : Fun A B G T ⟶ Fun A B G T} (hψ : ∀ X x, pt ψ X x = 1)
    (X : Under T) (x : (AffineWeil.groupScheme A B'' G'').affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)) :
    pt (conj Φ ψ) X x = 1 := by
  rw [pt_conj, hψ, map_one]

theorem restrict_conj {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)
    (ψ : Fun A B G T ⟶ Fun A B G T) :
    restrict χ (conj Φ ψ) = conj Φ (restrict χ ψ) := rfl

theorem conj_symm_conj (ψ : Fun A B G T ⟶ Fun A B G T) :
    conj Φ.symm (conj Φ ψ) = ψ := by
  simp only [conj, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rw [transportNat_hom_inv, Category.comp_id, reassoc_of% (transportNat_hom_inv Φ (T := T))]

section Transfer

variable {Φ}

omit [Module.Finite A B] [Module.Projective A B] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] in
/-- The rigidity statement, in terms of factor projections. -/
theorem rigidity (hR : WeilFactorIdempotentRigidityStatement.{u}) [Algebra.Etale A B'']
    (hred'' : IsReductive G'') (hsimple'' : ∀ s, IsAlmostSimple (geometricFiber G'' s))
    (ψ : Fun A B'' G'' T ⟶ Fun A B'' G'' T) (hidem : ψ ≫ ψ = ψ)
    (hnorm : ∀ (X : Under T) (h x : (AffineWeil.groupScheme A B'' G'').affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt ψ X (h * x * h⁻¹) = h * pt ψ X x * h⁻¹) :
    ∃ e'' : B'' ⊗[A] T, ∃ he'' : IsIdempotentElem e'',
      ψ = factorProjection A B'' G'' e'' he'' := by
  obtain ⟨e'', ⟨he'', hspec⟩, -⟩ := hR A B'' G'' hred'' hsimple'' T ψ hidem
    (fun X h x => hnorm X h x)
  exact ⟨e'', he'', eq_factorProjection he'' ψ (fun X x => hspec X x)⟩

omit [Module.Finite A B] [Module.Projective A B] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] in
/-- Factor projections determine their idempotents. -/
theorem factorProjection_injective (hR : WeilFactorIdempotentRigidityStatement.{u})
    [Algebra.Etale A B''] (hred'' : IsReductive G'')
    (hsimple'' : ∀ s, IsAlmostSimple (geometricFiber G'' s)) {e₁ e₂ : B'' ⊗[A] T}
    (h₁ : IsIdempotentElem e₁) (h₂ : IsIdempotentElem e₂)
    (h : factorProjection A B'' G'' e₁ h₁ = factorProjection A B'' G'' e₂ h₂) : e₁ = e₂ := by
  have hu := hR A B'' G'' hred'' hsimple'' T (factorProjection A B'' G'' e₁ h₁)
    (factorProjection_idem h₁) (fun X h x => pt_factorProjection_conj h₁ X h x)
  refine hu.unique ⟨h₁, fun X x => factorProjection_spec h₁ X x⟩ ⟨h₂, fun X x => ?_⟩
  rw [h]
  exact factorProjection_spec h₂ X x

variable (Φ)

open Classical in
/-- The idempotent of `B'' ⊗ T` whose factor projection is the conjugate by `Φ` of the factor
projection of `e` (and `0` if `e` is not idempotent). -/
def transfer (hR : WeilFactorIdempotentRigidityStatement.{u}) [Algebra.Etale A B'']
    (hred'' : IsReductive G'') (hsimple'' : ∀ s, IsAlmostSimple (geometricFiber G'' s))
    (e : B ⊗[A] T) : B'' ⊗[A] T :=
  if he : IsIdempotentElem e then
    Classical.choose (rigidity hR hred'' hsimple'' (conj Φ (factorProjection A B G e he))
      (conj_idem Φ (factorProjection_idem he))
      (conj_normal Φ (fun X h x => pt_factorProjection_conj he X h x)))
  else 0

variable (hR : WeilFactorIdempotentRigidityStatement.{u}) [Algebra.Etale A B'']
  (hred'' : IsReductive G'') (hsimple'' : ∀ s, IsAlmostSimple (geometricFiber G'' s))

theorem transfer_spec {e : B ⊗[A] T} (he : IsIdempotentElem e) :
    ∃ h'' : IsIdempotentElem (transfer Φ hR hred'' hsimple'' e),
      factorProjection A B'' G'' (transfer Φ hR hred'' hsimple'' e) h'' =
        conj Φ (factorProjection A B G e he) := by
  have hex := rigidity hR hred'' hsimple'' (conj Φ (factorProjection A B G e he))
    (conj_idem Φ (factorProjection_idem he))
    (conj_normal Φ (fun X h x => pt_factorProjection_conj he X h x))
  obtain ⟨h'', heq⟩ := Classical.choose_spec hex
  have hT : transfer Φ hR hred'' hsimple'' e = Classical.choose hex := by
    simp only [transfer, he, dite_true]
  have key : ∀ (e' : B'' ⊗[A] T) (he' : IsIdempotentElem e'), e' = Classical.choose hex →
      factorProjection A B'' G'' e' he' = conj Φ (factorProjection A B G e he) := by
    rintro e' he' rfl
    exact heq.symm
  exact ⟨hT ▸ h'', key _ _ hT⟩

theorem transfer_isIdempotentElem {e : B ⊗[A] T} (he : IsIdempotentElem e) :
    IsIdempotentElem (transfer Φ hR hred'' hsimple'' e) :=
  (transfer_spec Φ hR hred'' hsimple'' he).1

theorem factorProjection_transfer {e : B ⊗[A] T} (he : IsIdempotentElem e) :
    factorProjection A B'' G'' (transfer Φ hR hred'' hsimple'' e)
      (transfer_isIdempotentElem Φ hR hred'' hsimple'' he) =
        conj Φ (factorProjection A B G e he) :=
  (transfer_spec Φ hR hred'' hsimple'' he).2

theorem transfer_mul {e f : B ⊗[A] T} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    transfer Φ hR hred'' hsimple'' (f * e) =
      transfer Φ hR hred'' hsimple'' f * transfer Φ hR hred'' hsimple'' e := by
  apply factorProjection_injective hR hred'' hsimple''
    (transfer_isIdempotentElem Φ hR hred'' hsimple'' (hf.mul he))
    ((transfer_isIdempotentElem Φ hR hred'' hsimple'' hf).mul
      (transfer_isIdempotentElem Φ hR hred'' hsimple'' he))
  rw [factorProjection_transfer Φ hR hred'' hsimple'' (hf.mul he), ← factorProjection_comp he hf,
    ← factorProjection_comp (transfer_isIdempotentElem Φ hR hred'' hsimple'' he)
      (transfer_isIdempotentElem Φ hR hred'' hsimple'' hf),
    factorProjection_transfer Φ hR hred'' hsimple'' he,
    factorProjection_transfer Φ hR hred'' hsimple'' hf, conj_comp]

theorem transfer_lTensor {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)
    {e : B ⊗[A] T} (he : IsIdempotentElem e) :
    transfer Φ hR hred'' hsimple'' (Algebra.TensorProduct.lTensor (S := B) B χ.hom e) =
      Algebra.TensorProduct.lTensor (S := B'') B'' χ.hom (transfer Φ hR hred'' hsimple'' e) := by
  apply factorProjection_injective hR hred'' hsimple''
    (transfer_isIdempotentElem Φ hR hred'' hsimple'' (he.map _))
    ((transfer_isIdempotentElem Φ hR hred'' hsimple'' he).map _)
  rw [factorProjection_transfer Φ hR hred'' hsimple'' (he.map _),
    ← restrict_factorProjection χ he,
    ← restrict_factorProjection χ (transfer_isIdempotentElem Φ hR hred'' hsimple'' he),
    factorProjection_transfer Φ hR hred'' hsimple'' he, restrict_conj]

theorem transfer_zero :
    transfer Φ hR hred'' hsimple'' (0 : B ⊗[A] T) = 0 := by
  apply factorProjection_injective hR hred'' hsimple''
    (transfer_isIdempotentElem Φ hR hred'' hsimple'' IsIdempotentElem.zero) IsIdempotentElem.zero
  rw [factorProjection_transfer Φ hR hred'' hsimple'' IsIdempotentElem.zero]
  refine ext_pt fun X x => ?_
  rw [pt_conj_eq_one Φ (fun X x => pt_factorProjection_zero X x), pt_factorProjection_zero]

theorem transfer_symm_transfer [Algebra.Etale A B] (hred : IsReductive G)
    (hsimple : ∀ s, IsAlmostSimple (geometricFiber G s)) {e : B ⊗[A] T}
    (he : IsIdempotentElem e) :
    transfer Φ.symm hR hred hsimple (transfer Φ hR hred'' hsimple'' e) = e := by
  apply factorProjection_injective hR hred hsimple
    (transfer_isIdempotentElem Φ.symm hR hred hsimple
      (transfer_isIdempotentElem Φ hR hred'' hsimple'' he)) he
  rw [factorProjection_transfer Φ.symm hR hred hsimple
      (transfer_isIdempotentElem Φ hR hred'' hsimple'' he),
    factorProjection_transfer Φ hR hred'' hsimple'' he, conj_symm_conj]

end Transfer

end Langlands.GroupScheme.WeilFactor
