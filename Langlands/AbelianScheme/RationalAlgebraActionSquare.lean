import Langlands.AbelianScheme.RationalAlgebraAction
import Langlands.AbelianScheme.ConnectedEtaleRationalHomDescentStatement

/-! # Iterated pullbacks of rational algebra actions around a commuting square -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace Langlands.AbelianScheme.RationalAlgebraAction

variable {S W W' Z : Scheme.{u}} {D : Type v} [Ring D] [Algebra ℚ D]
  (g : W ⟶ S) (g' : W' ⟶ S) (a : Z ⟶ W) (a' : Z ⟶ W')

/-- For a commuting square `a ≫ g = a' ≫ g'`, the canonical equivariant
isomorphism between the two iterated pullbacks of a rational algebra action. -/
def pullbackSquareIso (hsq : a ≫ g = a' ≫ g') (X : RationalAlgebraAction S D) :
    (pullback a).obj ((pullback g).obj X) ≅ (pullback a').obj ((pullback g').obj X) :=
  (pullbackCompIso g a X).symm ≪≫
    eqToIso (congrArg (fun c => (pullback c).obj X) hsq) ≪≫ pullbackCompIso g' a' X

/-- Transport along an equality of base maps has, as underlying rational
homomorphism, the corresponding transport of abelian schemes. -/
theorem hom0_eqToHom_pullback {c c' : Z ⟶ S} (hc : c = c') (X : RationalAlgebraAction S D) :
    hom0 (eqToHom (congrArg (fun c => (pullback c).obj X) hc)) =
      homToHom0 (eqToHom (congrArg (fun c => (baseChange c).obj X.abelianScheme) hc)) := by
  subst hc
  rfl

/-- The underlying rational homomorphism of the equivariant square comparison is
the square comparison `baseChangeSquareIso` of the underlying abelian schemes. -/
theorem hom0_pullbackSquareIso_hom (hsq : a ≫ g = a' ≫ g') (X : RationalAlgebraAction S D) :
    hom0 (pullbackSquareIso g g' a a' hsq X).hom =
      homToHom0 (baseChangeSquareIso g g' a a' hsq X.abelianScheme).hom := by
  have h1 : hom0 (pullbackCompIso g a X).inv =
      homToHom0 (baseChangeCompIso g a X.abelianScheme).inv := rfl
  have h2 : hom0 (pullbackCompIso g' a' X).hom =
      homToHom0 (baseChangeCompIso g' a' X.abelianScheme).hom := rfl
  simp only [pullbackSquareIso, baseChangeSquareIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, hom0_comp]
  rw [h1, h2, hom0_eqToHom_pullback hsq]
  exact (congrArg (fun r => comp0 _ _ _
      (homToHom0 (baseChangeCompIso g a X.abelianScheme).inv) r)
    (comp0_homToHom0 _ _)).trans (comp0_homToHom0 _ _)

/-- If pulled-back equivariant isomorphisms commute with the equivariant square
comparisons, their underlying rational homomorphisms satisfy the compatibility
equation of `ConnectedEtaleRationalHomDescentStatement`. -/
theorem square_compatible_of_iso_eq (hsq : a ≫ g = a' ≫ g')
    {X Y : RationalAlgebraAction S D}
    (e : (pullback g).obj X ≅ (pullback g).obj Y) (e' : (pullback g').obj X ≅ (pullback g').obj Y)
    (he : (pullback a).mapIso e ≪≫ pullbackSquareIso g g' a a' hsq Y =
      pullbackSquareIso g g' a a' hsq X ≪≫ (pullback a').mapIso e') :
    comp0 _ _ _ (rationalBaseChangeHom a (hom0 e.hom))
        (homToHom0 (baseChangeSquareIso g g' a a' hsq Y.abelianScheme).hom) =
      comp0 _ _ _ (homToHom0 (baseChangeSquareIso g g' a a' hsq X.abelianScheme).hom)
        (rationalBaseChangeHom a' (hom0 e'.hom)) := by
  have k := congrArg (fun i => hom0 i.hom) he
  simp only [Iso.trans_hom, Functor.mapIso_hom, hom0_comp, hom0_pullback_map,
    hom0_pullbackSquareIso_hom] at k
  exact k

omit [Algebra ℚ D] in
private theorem inverse_square {C : Type*} [Category C] {P Q P' Q' : C}
    (e : P ≅ Q) (e' : P' ≅ Q') (i : P ≅ P') (j : Q ≅ Q')
    (h : e ≪≫ j = i ≪≫ e') : e.symm ≪≫ i = j ≪≫ e'.symm := by
  have h' := congrArg (fun k => e.symm ≪≫ (k ≪≫ e'.symm)) h
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl]
    using h'.symm

set_option maxHeartbeats 3200000 in
/-- Rational Hom descent glues compatible equivariant isomorphisms between the
restrictions of two fixed actions, if rational morphisms are detected by pullback
to a chosen member of the cover. -/
theorem exists_iso_of_etale_rationalHomDescent
    (descent : ConnectedEtaleRationalHomDescentStatement.{u})
    [IsLocallyNoetherian S] [ConnectedSpace S]
    (hu : ∀ t : GroupScheme.Tate.Index (fun _ => True), IsUnit (t.val : Γ(S, ⊤)))
    {K : Type u} (W : K → Scheme.{u})
    [∀ k, IsLocallyNoetherian (W k)] [∀ k, ConnectedSpace (W k)]
    (f : ∀ k, W k ⟶ S) (hf : ∀ k, Etale (f k))
    (hsurj : ∀ x : S, ∃ (k : K) (y : W k), f k y = x)
    (k₀ : K)
    (hinj : ∀ (A B : AbelianScheme S), Function.Injective (rationalBaseChangeHom (f k₀)
      (A := A) (B := B))) {X Y : RationalAlgebraAction S D}
    (e : ∀ k, (pullback (f k)).obj X ≅ (pullback (f k)).obj Y)
    (he : ∀ (k l : K) (T : Scheme.{u}) [IsLocallyNoetherian T] [ConnectedSpace T]
      (a : T ⟶ W k) (b : T ⟶ W l) (hsq : a ≫ f k = b ≫ f l),
        (pullback a).mapIso (e k) ≪≫ pullbackSquareIso (f k) (f l) a b hsq Y =
          pullbackSquareIso (f k) (f l) a b hsq X ≪≫ (pullback b).mapIso (e l)) :
    ∃ iso : X ≅ Y, ∀ k, (pullback (f k)).mapIso iso = e k := by
  let A := X.abelianScheme
  let B := Y.abelianScheme
  obtain ⟨m, hm⟩ := descent S hu K W f hf hsurj X.abelianScheme Y.abelianScheme
    (fun k => hom0 (e k).hom) (fun k l T _ _ a b hsq =>
      square_compatible_of_iso_eq (f k) (f l) a b hsq (X := X) (Y := Y)
        (e k) (e l) (he k l T a b hsq))
  obtain ⟨n, hn⟩ := descent S hu K W f hf hsurj Y.abelianScheme X.abelianScheme
    (fun k => hom0 (e k).inv) (by
      intro k l T _ _ a b hsq
      apply square_compatible_of_iso_eq (f k) (f l) a b hsq (X := Y) (Y := X) (e k).symm (e l).symm
      simpa only [Functor.mapIso_symm] using
        inverse_square ((pullback a).mapIso (e k)) ((pullback b).mapIso (e l))
          (pullbackSquareIso (f k) (f l) a b hsq X)
          (pullbackSquareIso (f k) (f l) a b hsq Y) (he k l T a b hsq))
  have mapComp (A₁ A₂ A₃ : AbelianScheme S) (r : Hom0 A₁ A₂) (t : Hom0 A₂ A₃) :
      rationalBaseChangeHom (f k₀) (comp0 A₁ A₂ A₃ r t) =
        comp0 ((baseChange (f k₀)).obj A₁) ((baseChange (f k₀)).obj A₂)
          ((baseChange (f k₀)).obj A₃) (rationalBaseChangeHom (f k₀) r)
          (rationalBaseChangeHom (f k₀) t) :=
    rationalBaseChangeHom_comp (f k₀) (A := A₁) (B := A₂) (C := A₃) r t
  have mapId (P : AbelianScheme S) :
      rationalBaseChangeHom (f k₀) (id0 P) = id0 ((baseChange (f k₀)).obj P) :=
    rationalBaseChangeHom_identity (f k₀) P
  have inverseComp {P Q : RationalAlgebraAction S D}
      (r : Hom0 P.abelianScheme Q.abelianScheme) (t : Hom0 Q.abelianScheme P.abelianScheme)
      (i : (pullback (f k₀)).obj P ≅ (pullback (f k₀)).obj Q)
      (hr : rationalBaseChangeHom (f k₀) r = hom0 i.hom)
      (ht : rationalBaseChangeHom (f k₀) t = hom0 i.inv) :
      comp0 _ _ _ r t = id0 P.abelianScheme := by
    let P' := (pullback (f k₀)).obj P
    let Q' := (pullback (f k₀)).obj Q
    let P₀ := P'.abelianScheme
    let Q₀ := Q'.abelianScheme
    apply hinj P.abelianScheme P.abelianScheme
    calc
      _ = comp0 P₀ Q₀ P₀ (rationalBaseChangeHom (f k₀) r) (rationalBaseChangeHom (f k₀) t) :=
        mapComp P.abelianScheme Q.abelianScheme P.abelianScheme r t
      _ = comp0 P₀ Q₀ P₀ (hom0 i.hom) (hom0 i.inv) :=
        congrArg₂ (fun x y => comp0 P₀ Q₀ P₀ x y) hr ht
      _ = id0 P₀ := congrArg (hom0 (X := P') (Y := P')) i.hom_inv_id
      _ = _ := (mapId P.abelianScheme).symm
  have hmn : comp0 A B A m n = id0 A :=
    inverseComp (P := X) (Q := Y) m n (e k₀) (hm k₀) (hn k₀)
  have hnm : comp0 B A B n m = id0 B :=
    inverseComp (P := Y) (Q := X) n m (e k₀).symm (hn k₀) (hm k₀)
  have hAction (d : D) : comp0 A A B (X.action d).asHom m = comp0 A B B m (Y.action d).asHom := by
    let X₀ := (pullback (f k₀)).obj X
    let Y₀ := (pullback (f k₀)).obj Y
    let A₀ := X₀.abelianScheme
    let B₀ := Y₀.abelianScheme
    apply hinj A B
    calc
      _ = comp0 A₀ A₀ B₀ (X₀.action d).asHom (rationalBaseChangeHom (f k₀) m) :=
        mapComp A A B (X.action d).asHom m
      _ = comp0 A₀ A₀ B₀ (X₀.action d).asHom (hom0 (e k₀).hom) :=
        congrArg (comp0 A₀ A₀ B₀ (X₀.action d).asHom) (hm k₀)
      _ = comp0 A₀ B₀ B₀ (hom0 (e k₀).hom) (Y₀.action d).asHom :=
        intertwines (X := X₀) (Y := Y₀) (e k₀).hom d
      _ = comp0 A₀ B₀ B₀ (rationalBaseChangeHom (f k₀) m) (Y₀.action d).asHom :=
        congrArg (fun r => comp0 A₀ B₀ B₀ r (Y₀.action d).asHom) (hm k₀).symm
      _ = _ := (mapComp A B B m (Y.action d).asHom).symm
  let iso : X ≅ Y := isoMk (X := X) (Y := Y)
    { hom := m, inv := n, hom_inv_id := hmn, inv_hom_id := hnm } hAction
  refine ⟨iso, fun k => ?_⟩
  apply Iso.ext
  apply hom_ext
  exact hm k

end Langlands.AbelianScheme.RationalAlgebraAction
