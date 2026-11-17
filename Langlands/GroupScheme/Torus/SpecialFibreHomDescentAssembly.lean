import Langlands.GroupScheme.Torus.CompleteLocalSimultaneousSplitting
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Special-fibre Hom transport and the finite-cover assembly -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem baseChangeEqIso_naturality {S T : Scheme.{u}} {b b' : T ⟶ S}
    (h : b = b') {H G : GroupScheme S} (f : H ⟶ G) :
    (GroupScheme.baseChange b).map f ≫
        (eqToIso (congrArg (fun c => (GroupScheme.baseChange c).obj G) h)).hom =
      (eqToIso (congrArg (fun c => (GroupScheme.baseChange c).obj H) h)).hom ≫
        (GroupScheme.baseChange b').map f := by
  cases h
  simp

variable {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]
  {H G : GroupScheme (Spec (CommRingCat.of A))}

/-- The actual special-fibre comparison is natural in the group homomorphism. -/
theorem specialFibreBaseChangeIso_naturality (f : H ⟶ G) :
    (GroupScheme.baseChange (Spec.algebraMap B (IsLocalRing.ResidueField B))).map
        ((GroupScheme.baseChange (Spec.algebraMap A B)).map f) ≫
        (specialFibreBaseChangeIso G).hom =
      (specialFibreBaseChangeIso H).hom ≫
        (GroupScheme.baseChange
          (Spec.algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))).map
          ((GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f) := by
  let c := Spec.algebraMap A B
  let s := Spec.algebraMap A (IsLocalRing.ResidueField A)
  let s' := Spec.algebraMap B (IsLocalRing.ResidueField B)
  let r := Spec.algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  have hc : s' ≫ c = r ≫ s := by
    simp only [c, s, s', r, Spec.algebraMap, ← Spec.map_comp]
    congr 1
  let eH₁ := baseChangeCompIso c s' H
  let eG₁ := baseChangeCompIso c s' G
  let eH₂ := baseChangeCompIso s r H
  let eG₂ := baseChangeCompIso s r G
  let qH := eqToIso (congrArg (fun b => (GroupScheme.baseChange b).obj H) hc)
  let qG := eqToIso (congrArg (fun b => (GroupScheme.baseChange b).obj G) hc)
  have h₁ : (GroupScheme.baseChange s').map ((GroupScheme.baseChange c).map f) ≫ eG₁.inv =
      eH₁.inv ≫ (GroupScheme.baseChange (s' ≫ c)).map f :=
    (((Functor.mapGrpNatIso (Over.pullbackComp s' c)) ≪≫
      Functor.mapGrpCompIso).inv.naturality f)
  have h₂ : (GroupScheme.baseChange (s' ≫ c)).map f ≫ qG.hom =
      qH.hom ≫ (GroupScheme.baseChange (r ≫ s)).map f :=
    baseChangeEqIso_naturality hc f
  have h₃ : (GroupScheme.baseChange (r ≫ s)).map f ≫ eG₂.hom =
      eH₂.hom ≫ (GroupScheme.baseChange r).map ((GroupScheme.baseChange s).map f) :=
    (((Functor.mapGrpNatIso (Over.pullbackComp r s)) ≪≫
      Functor.mapGrpCompIso).hom.naturality f)
  change (GroupScheme.baseChange s').map ((GroupScheme.baseChange c).map f) ≫
      (eG₁.inv ≫ qG.hom ≫ eG₂.hom) =
    (eH₁.inv ≫ qH.hom ≫ eH₂.hom) ≫
      (GroupScheme.baseChange r).map ((GroupScheme.baseChange s).map f)
  calc
    _ = eH₁.inv ≫ (GroupScheme.baseChange (s' ≫ c)).map f ≫ qG.hom ≫ eG₂.hom := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ qG.hom ≫ eG₂.hom) h₁
    _ = eH₁.inv ≫ qH.hom ≫ (GroupScheme.baseChange (r ≫ s)).map f ≫ eG₂.hom := by
      simpa only [Category.assoc] using congrArg (fun k => eH₁.inv ≫ k ≫ eG₂.hom) h₂
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun k => eH₁.inv ≫ qH.hom ≫ k) h₃

/-- Pull an actual special-fibre homomorphism to the residue field of a local
extension and identify it with the special fibre of the base-changed groups. -/
def specialHomTransport (f₀ :
    (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj H ⟶
      (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G) :
    (GroupScheme.baseChange (Spec.algebraMap B (IsLocalRing.ResidueField B))).obj
        ((GroupScheme.baseChange (Spec.algebraMap A B)).obj H) ⟶
      (GroupScheme.baseChange (Spec.algebraMap B (IsLocalRing.ResidueField B))).obj
        ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G) :=
  (specialFibreBaseChangeIso H).hom ≫
    (GroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))).map f₀ ≫
    (specialFibreBaseChangeIso G).inv

/-- Transport of a global special fibre is the actual special fibre of its
base-changed homomorphism. -/
theorem specialHomTransport_baseChange (f : H ⟶ G) :
    specialHomTransport (B := B)
        ((GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f) =
      (GroupScheme.baseChange (Spec.algebraMap B (IsLocalRing.ResidueField B))).map
        ((GroupScheme.baseChange (Spec.algebraMap A B)).map f) := by
  apply (cancel_mono (specialFibreBaseChangeIso G).hom).mp
  simpa only [specialHomTransport, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    using (specialFibreBaseChangeIso_naturality (B := B) f).symm

/-- Equality with the transported special homomorphism is exactly the
commutative special-fibre comparison square. -/
theorem specialHomTransport_eq_iff
    (f₀ :
      (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj H ⟶
        (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G)
    (fB : (GroupScheme.baseChange (Spec.algebraMap A B)).obj H ⟶
      (GroupScheme.baseChange (Spec.algebraMap A B)).obj G) :
    (GroupScheme.baseChange (Spec.algebraMap B (IsLocalRing.ResidueField B))).map fB =
        specialHomTransport (B := B) f₀ ↔
      (GroupScheme.baseChange (Spec.algebraMap B (IsLocalRing.ResidueField B))).map fB ≫
          (specialFibreBaseChangeIso G).hom =
        (specialFibreBaseChangeIso H).hom ≫
          (GroupScheme.baseChange
            (Spec.algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))).map f₀ := by
  constructor
  · intro h
    rw [h]
    simp only [specialHomTransport, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro h
    apply (cancel_mono (specialFibreBaseChangeIso G).hom).mp
    simpa only [specialHomTransport, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- Split-cover special-fibre Hom bijectivity and existence of descents imply
the original special-fibre Hom bijectivity. -/
theorem specialFibre_hom_bijective_of_cover
    [Flat (Spec.algebraMap A B)] [Surjective (Spec.algebraMap A B)]
    [QuasiCompact (Spec.algebraMap A B)]
    (hB : Function.Bijective
      (fun f : (GroupScheme.baseChange (Spec.algebraMap A B)).obj H ⟶
          (GroupScheme.baseChange (Spec.algebraMap A B)).obj G =>
        (GroupScheme.baseChange (Spec.algebraMap B (IsLocalRing.ResidueField B))).map f))
    (hdesc : ∀ f₀ :
        (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj H ⟶
          (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G,
      ∀ fB : (GroupScheme.baseChange (Spec.algebraMap A B)).obj H ⟶
          (GroupScheme.baseChange (Spec.algebraMap A B)).obj G,
        (GroupScheme.baseChange (Spec.algebraMap B (IsLocalRing.ResidueField B))).map fB =
          specialHomTransport (B := B) f₀ →
        ∃ f : H ⟶ G,
          (GroupScheme.baseChange (Spec.algebraMap A B)).map f = fB ∧
          (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f = f₀) :
    Function.Bijective (fun f : H ⟶ G =>
      (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f) := by
  constructor
  · intro f g hfg
    apply (GroupScheme.baseChange (Spec.algebraMap A B)).map_injective
    apply hB.injective
    exact (specialHomTransport_baseChange (B := B) f).symm.trans
      ((congrArg (specialHomTransport (B := B)) hfg).trans
        (specialHomTransport_baseChange (B := B) g))
  · intro f₀
    obtain ⟨fB, hfB⟩ := hB.surjective (specialHomTransport (B := B) f₀)
    obtain ⟨f, -, hf⟩ := hdesc f₀ fB hfB
    exact ⟨f, hf⟩

end Langlands.GroupScheme.CompleteLocalDeformation
