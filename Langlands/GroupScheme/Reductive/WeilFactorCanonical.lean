import Langlands.GroupScheme.Reductive.WeilFactorUniquenessReduction

/-! # The canonical algebra isomorphism attached to an isomorphism of Weil restrictions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilFactor

open Langlands.Algebra.GraphIdempotent

section Transport

variable {A B B'' B''' : Type u} [CommRing A] [CommRing B] [CommRing B''] [CommRing B''']
  [Algebra A B] [Algebra A B''] [Algebra A B'''] [Module.Finite A B] [Module.Projective A B]
  [Module.Finite A B''] [Module.Projective A B''] [Module.Finite A B''']
  [Module.Projective A B''']
  {G : GroupScheme (Spec (CommRingCat.of B))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {G'' : GroupScheme (Spec (CommRingCat.of B''))} [IsAffine G''.X.left]
  [LocallyOfFiniteType G''.X.hom]
  {G''' : GroupScheme (Spec (CommRingCat.of B'''))} [IsAffine G'''.X.left]
  [LocallyOfFiniteType G'''.X.hom]
  {T : CommAlgCat.{u} (CommRingCat.of A)}

theorem transportNat_id :
    transportNat (𝟙 (AffineWeil.groupScheme A B G)) T = 𝟙 _ := by
  refine ext_pt fun X x => ?_
  exact Category.comp_id x

theorem transportNat_comp
    (f : AffineWeil.groupScheme A B G ⟶ AffineWeil.groupScheme A B'' G'')
    (g : AffineWeil.groupScheme A B'' G'' ⟶ AffineWeil.groupScheme A B''' G''') :
    transportNat (f ≫ g) T = transportNat f T ≫ transportNat g T := by
  refine NatTrans.ext (funext fun X => GrpCat.ext ?_)
  intro (x : (AffineWeil.groupScheme A B G).affinePoints
    (CommAlgCat.of (CommRingCat.of A) X.right))
  change x ≫ (f ≫ g).hom.hom = (x ≫ f.hom.hom) ≫ g.hom.hom
  rw [Category.assoc]
  rfl

theorem conj_refl (ψ : Fun A B G T ⟶ Fun A B G T) :
    conj (Iso.refl (AffineWeil.groupScheme A B G)) ψ = ψ := by
  simp only [conj, Iso.refl_hom, Iso.refl_inv, transportNat_id, Category.id_comp,
    Category.comp_id]

theorem conj_trans (Φ₁ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'')
    (Φ₂ : AffineWeil.groupScheme A B'' G'' ≅ AffineWeil.groupScheme A B''' G''')
    (ψ : Fun A B G T ⟶ Fun A B G T) :
    conj (Φ₁ ≪≫ Φ₂) ψ = conj Φ₂ (conj Φ₁ ψ) := by
  simp only [conj, Iso.trans_hom, Iso.trans_inv, transportNat_comp, Category.assoc]

variable (hR : WeilFactorIdempotentRigidityStatement.{u})

theorem transfer_refl [Algebra.Etale A B] (hred : IsReductive G)
    (hsimple : ∀ s, IsAlmostSimple (geometricFiber G s)) {e : B ⊗[A] T}
    (he : IsIdempotentElem e) :
    transfer (Iso.refl (AffineWeil.groupScheme A B G)) hR hred hsimple e = e := by
  apply factorProjection_injective hR hred hsimple
    (transfer_isIdempotentElem _ hR hred hsimple he) he
  rw [factorProjection_transfer _ hR hred hsimple he, conj_refl]

theorem transfer_trans [Algebra.Etale A B''] [Algebra.Etale A B''']
    (Φ₁ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'')
    (Φ₂ : AffineWeil.groupScheme A B'' G'' ≅ AffineWeil.groupScheme A B''' G''')
    (hred'' : IsReductive G'') (hsimple'' : ∀ s, IsAlmostSimple (geometricFiber G'' s))
    (hred''' : IsReductive G''') (hsimple''' : ∀ s, IsAlmostSimple (geometricFiber G''' s))
    {e : B ⊗[A] T} (he : IsIdempotentElem e) :
    transfer (Φ₁ ≪≫ Φ₂) hR hred''' hsimple''' e =
      transfer Φ₂ hR hred''' hsimple''' (transfer Φ₁ hR hred'' hsimple'' e) := by
  have he'' := transfer_isIdempotentElem Φ₁ hR hred'' hsimple'' he
  apply factorProjection_injective hR hred''' hsimple'''
    (transfer_isIdempotentElem _ hR hred''' hsimple''' he)
    (transfer_isIdempotentElem Φ₂ hR hred''' hsimple''' he'')
  rw [factorProjection_transfer _ hR hred''' hsimple''' he,
    factorProjection_transfer Φ₂ hR hred''' hsimple''' he'',
    factorProjection_transfer Φ₁ hR hred'' hsimple'' he, conj_trans]

end Transport

section Canonical

variable {A B B'' B''' : Type u} [CommRing A] [CommRing B] [CommRing B''] [CommRing B''']
  [Algebra A B] [Algebra A B''] [Algebra A B'''] [Module.Finite A B] [Module.Projective A B]
  [Module.Finite A B''] [Module.Projective A B''] [Module.Finite A B''']
  [Module.Projective A B'''] [Algebra.Etale A B] [Algebra.Etale A B''] [Algebra.Etale A B''']
  {G : GroupScheme (Spec (CommRingCat.of B))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {G'' : GroupScheme (Spec (CommRingCat.of B''))} [IsAffine G''.X.left]
  [LocallyOfFiniteType G''.X.hom]
  {G''' : GroupScheme (Spec (CommRingCat.of B'''))} [IsAffine G'''.X.left]
  [LocallyOfFiniteType G'''.X.hom]
  (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive G) (hsimple : ∀ s, IsAlmostSimple (geometricFiber G s))
  (hred'' : IsReductive G'') (hsimple'' : ∀ s, IsAlmostSimple (geometricFiber G'' s))
  (hred''' : IsReductive G''') (hsimple''' : ∀ s, IsAlmostSimple (geometricFiber G''' s))

/-- The property of `α : B'' ≃ B` attached to `Φ`: the transfer by `Φ` of the graph idempotent of
any `φ : B → T` is the graph idempotent of `φ ∘ α`. -/
def IsWeilAlgEquiv (Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'')
    (α : B'' ≃ₐ[A] B) : Prop :=
  ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (φ : B →ₐ[A] T) (e : B ⊗[A] T),
    IsGraphIdempotent φ e →
      IsGraphIdempotent (φ.comp (α : B'' →ₐ[A] B)) (transfer Φ hR hred'' hsimple'' e)

/-- The canonical `A`-algebra isomorphism `B'' ≃ B` attached to an isomorphism of Weil
restrictions. -/
def weilAlgEquiv (Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'') :
    B'' ≃ₐ[A] B :=
  Classical.choose (exists_algEquiv_transfer Φ hR hred hsimple hred'' hsimple'')

theorem weilAlgEquiv_spec (Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'') :
    IsWeilAlgEquiv hR hred'' hsimple'' Φ (weilAlgEquiv hR hred hsimple hred'' hsimple'' Φ) :=
  Classical.choose_spec (exists_algEquiv_transfer Φ hR hred hsimple hred'' hsimple'')

set_option backward.isDefEq.respectTransparency false in
theorem IsWeilAlgEquiv.eq
    {Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G''} {α α' : B'' ≃ₐ[A] B}
    (h : IsWeilAlgEquiv hR hred'' hsimple'' Φ α) (h' : IsWeilAlgEquiv hR hred'' hsimple'' Φ α') :
    α = α' := by
  let TB : CommAlgCat.{u} (CommRingCat.of A) := CommAlgCat.of (CommRingCat.of A) B
  obtain ⟨δ, hδ⟩ := exists_isGraphIdempotent (A := A) (B := B) (T := TB) (AlgHom.id A B)
  have h1 := (h TB (AlgHom.id A B) δ hδ).algHom_eq (h' TB (AlgHom.id A B) δ hδ)
  ext b
  exact congrArg (fun f : B'' →ₐ[A] B => f b) h1

/-- Uniqueness: any `α` with the defining property is `weilAlgEquiv Φ`. -/
theorem weilAlgEquiv_unique (Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'')
    {α : B'' ≃ₐ[A] B} (h : IsWeilAlgEquiv hR hred'' hsimple'' Φ α) :
    α = weilAlgEquiv hR hred hsimple hred'' hsimple'' Φ :=
  h.eq hR hred'' hsimple'' (weilAlgEquiv_spec hR hred hsimple hred'' hsimple'' Φ)

theorem weilAlgEquiv_refl :
    weilAlgEquiv hR hred hsimple hred hsimple (Iso.refl (AffineWeil.groupScheme A B G)) =
      AlgEquiv.refl := by
  symm
  apply weilAlgEquiv_unique
  intro T φ e he
  rw [transfer_refl hR hred hsimple he.isIdempotentElem]
  exact he

theorem weilAlgEquiv_trans
    (Φ₁ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'')
    (Φ₂ : AffineWeil.groupScheme A B'' G'' ≅ AffineWeil.groupScheme A B''' G''') :
    weilAlgEquiv hR hred hsimple hred''' hsimple''' (Φ₁ ≪≫ Φ₂) =
      (weilAlgEquiv hR hred'' hsimple'' hred''' hsimple''' Φ₂).trans
        (weilAlgEquiv hR hred hsimple hred'' hsimple'' Φ₁) := by
  symm
  apply weilAlgEquiv_unique
  intro T φ e he
  rw [transfer_trans hR Φ₁ Φ₂ hred'' hsimple'' hred''' hsimple''' he.isIdempotentElem]
  have h1 := weilAlgEquiv_spec hR hred hsimple hred'' hsimple'' Φ₁ T φ e he
  exact weilAlgEquiv_spec hR hred'' hsimple'' hred''' hsimple''' Φ₂ T _ _ h1

end Canonical

end Langlands.GroupScheme.WeilFactor
