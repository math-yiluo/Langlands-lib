import Langlands.Representation.Exponents.WeylBranchPiecesStatement
import Langlands.Representation.Twist.Definitions
import Langlands.Representation.Filtration.Definitions
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RepresentationTheory.Irreducible

/-!
# Elementary laws for actual subquotients

Closure of `WeylBranchPieces.IsSubquotient` under surjections, composition,
character twists and restriction along group homomorphisms; graded pieces of
finite natural filtrations as subquotients, and the location of an irreducible
subquotient in one graded piece.
-/

noncomputable section

namespace Langlands.WeylBranchPieces

universe uG uH uV uW uX uC vC

section Laws

variable {G : Type uG} [Group G] {H : Type uH} [Group H]
  {V : Type uV} {W : Type uW} {X : Type uX}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

/-- The inclusion of an actual subrepresentation. -/
def subtypeMap {A : Representation ℂ G V} (U : Subrepresentation A) :
    U.toRepresentation.IntertwiningMap A where
  toLinearMap := U.toSubmodule.subtype
  isIntertwining' _ := by
    ext v
    rfl

/-- A surjective intertwiner exhibits its target as a subquotient. -/
theorem IsSubquotient.of_surjective {A : Representation ℂ G V}
    {Y : Representation ℂ G W} (f : A.IntertwiningMap Y)
    (hf : Function.Surjective f) : IsSubquotient A Y := by
  refine ⟨⊤, f.comp (subtypeMap ⊤), fun y => ?_⟩
  obtain ⟨v, rfl⟩ := hf y
  exact ⟨⟨v, Submodule.mem_top⟩, rfl⟩

/-- Every representation is a subquotient of itself. -/
theorem IsSubquotient.refl (A : Representation ℂ G V) : IsSubquotient A A :=
  IsSubquotient.of_surjective (Representation.IntertwiningMap.id A) fun v => ⟨v, rfl⟩

/-- An actual intertwining equivalence exhibits its target as a subquotient. -/
theorem IsSubquotient.of_equiv {A : Representation ℂ G V}
    {Y : Representation ℂ G W} (e : A.Equiv Y) : IsSubquotient A Y :=
  IsSubquotient.of_surjective e.toIntertwiningMap e.surjective

/-- A subquotient of a subquotient is a subquotient: the preimage of the
inner subrepresentation is an actual subrepresentation of the outer one. -/
theorem IsSubquotient.trans {A : Representation ℂ G V}
    {Y : Representation ℂ G W} {Z : Representation ℂ G X}
    (h₁ : IsSubquotient A Y) (h₂ : IsSubquotient Y Z) : IsSubquotient A Z := by
  obtain ⟨U, q, hq⟩ := h₁
  obtain ⟨U', q', hq'⟩ := h₂
  let P : Submodule ℂ V :=
    { carrier := {v | ∃ hv : v ∈ U.toSubmodule, q ⟨v, hv⟩ ∈ U'.toSubmodule}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨U.toSubmodule.add_mem ha hb, ?_⟩
        have e : (⟨a + b, U.toSubmodule.add_mem ha hb⟩ : U.toSubmodule) =
            ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [e, map_add]
        exact U'.toSubmodule.add_mem ha' hb'
      zero_mem' := by
        refine ⟨U.toSubmodule.zero_mem, ?_⟩
        have e : (⟨0, U.toSubmodule.zero_mem⟩ : U.toSubmodule) = 0 := rfl
        rw [e, map_zero]
        exact U'.toSubmodule.zero_mem
      smul_mem' := by
        rintro c a ⟨ha, ha'⟩
        refine ⟨U.toSubmodule.smul_mem c ha, ?_⟩
        have e : (⟨c • a, U.toSubmodule.smul_mem c ha⟩ : U.toSubmodule) =
            c • ⟨a, ha⟩ := rfl
        rw [e, map_smul]
        exact U'.toSubmodule.smul_mem c ha' }
  have hqg : ∀ (g : G) (v : V) (hv : v ∈ U.toSubmodule),
      q ⟨A g v, U.apply_mem_toSubmodule g hv⟩ = Y g (q ⟨v, hv⟩) := fun g v hv =>
    Representation.IntertwiningMap.isIntertwining U.toRepresentation Y q g ⟨v, hv⟩
  let U'' : Subrepresentation A :=
    { toSubmodule := P
      apply_mem_toSubmodule := by
        rintro g v ⟨hv, hv'⟩
        refine ⟨U.apply_mem_toSubmodule g hv, ?_⟩
        rw [hqg g v hv]
        exact U'.apply_mem_toSubmodule g hv' }
  let r : P →ₗ[ℂ] U'.toSubmodule :=
    { toFun := fun v => ⟨q ⟨v.1, v.2.fst⟩, v.2.snd⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        change q (⟨a.1, a.2.fst⟩ + ⟨b.1, b.2.fst⟩) = q ⟨a.1, a.2.fst⟩ + q ⟨b.1, b.2.fst⟩
        exact map_add q _ _
      map_smul' := by
        intro c a
        apply Subtype.ext
        change q (c • ⟨a.1, a.2.fst⟩) = c • q ⟨a.1, a.2.fst⟩
        exact map_smul q _ _ }
  let r' : U''.toRepresentation.IntertwiningMap U'.toRepresentation :=
    { toLinearMap := r
      isIntertwining' := by
        intro g
        ext v
        exact hqg g v.1 v.2.fst }
  refine ⟨U'', q'.comp r', fun z => ?_⟩
  obtain ⟨y, rfl⟩ := hq' z
  obtain ⟨u, hu⟩ := hq y.1
  refine ⟨⟨u.1, u.2, ?_⟩, ?_⟩
  · change q u ∈ U'.toSubmodule
    rw [hu]
    exact y.2
  · change q' (r ⟨u.1, _⟩) = q' y
    congr 1
    apply Subtype.ext
    exact hu

/-- An equivalence of the target preserves being a subquotient. -/
theorem IsSubquotient.of_equiv_right {A : Representation ℂ G V}
    {Y : Representation ℂ G W} {Z : Representation ℂ G X}
    (h : IsSubquotient A Y) (e : Y.Equiv Z) : IsSubquotient A Z :=
  h.trans (IsSubquotient.of_equiv e)

/-- An equivalence of the source preserves being a subquotient. -/
theorem IsSubquotient.of_equiv_left {A : Representation ℂ G V}
    {Y : Representation ℂ G W} {Z : Representation ℂ G X}
    (e : A.Equiv Y) (h : IsSubquotient Y Z) : IsSubquotient A Z :=
  (IsSubquotient.of_equiv e).trans h

/-- A surjection onto the source preserves being a subquotient. -/
theorem IsSubquotient.of_surjective_left {A : Representation ℂ G V}
    {Y : Representation ℂ G W} {Z : Representation ℂ G X}
    (f : A.IntertwiningMap Y) (hf : Function.Surjective f)
    (h : IsSubquotient Y Z) : IsSubquotient A Z :=
  (IsSubquotient.of_surjective f hf).trans h

/-- Restriction along a group homomorphism preserves subquotients. -/
theorem IsSubquotient.comp {A : Representation ℂ G V} {Y : Representation ℂ G W}
    (h : IsSubquotient A Y) (φ : H →* G) : IsSubquotient (A.comp φ) (Y.comp φ) := by
  obtain ⟨U, q, hq⟩ := h
  let U' : Subrepresentation (A.comp φ) :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := fun x _ hv => U.apply_mem_toSubmodule (φ x) hv }
  let q' : U'.toRepresentation.IntertwiningMap (Y.comp φ) :=
    { toLinearMap := q.toLinearMap
      isIntertwining' := by
        intro x
        ext v
        exact Representation.IntertwiningMap.isIntertwining U.toRepresentation Y q (φ x) v }
  exact ⟨U', q', hq⟩

/-- Restriction along the inverse of a group equivalence moves to the target. -/
theorem IsSubquotient.of_comp_symm {A : Representation ℂ G V}
    {Y : Representation ℂ H W} (e : G ≃* H)
    (h : IsSubquotient (A.comp e.symm.toMonoidHom) Y) :
    IsSubquotient A (Y.comp e.toMonoidHom) := by
  have h' := h.comp e.toMonoidHom
  have hA : (A.comp e.symm.toMonoidHom).comp e.toMonoidHom = A := by
    ext g v
    simp
  rwa [hA] at h'

/-- A common character twist preserves subquotients. -/
theorem IsSubquotient.twist {A : Representation ℂ G V} {Y : Representation ℂ G W}
    (h : IsSubquotient A Y) (χ : G →* ℂˣ) :
    IsSubquotient (Langlands.twist χ A) (Langlands.twist χ Y) := by
  obtain ⟨U, q, hq⟩ := h
  let U' : Subrepresentation (Langlands.twist χ A) :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := fun g _ hv =>
        U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule g hv) }
  let q' : U'.toRepresentation.IntertwiningMap (Langlands.twist χ Y) :=
    { toLinearMap := q.toLinearMap
      isIntertwining' := by
        intro g
        ext v
        change q ((χ g : ℂ) • ⟨A g v.1, U.apply_mem_toSubmodule g v.2⟩) =
          (χ g : ℂ) • Y g (q v)
        rw [map_smul]
        congr 1
        exact Representation.IntertwiningMap.isIntertwining U.toRepresentation Y q g v }
  exact ⟨U', q', hq⟩

end Laws

section Graded

open CategoryTheory

variable {G : Type uG} [Group G] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {C : Type uC} [Category.{vC} C]

/-- A surjective intertwiner whose kernel lies in the kernel of a second
intertwiner lets the second one descend to its target. -/
theorem exists_descend {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (g : ρ.IntertwiningMap σ) (f : ρ.IntertwiningMap τ)
    (hg : Function.Surjective g) (hker : g.toLinearMap.ker ≤ f.toLinearMap.ker) :
    ∃ h : σ.IntertwiningMap τ, ∀ x, h (g x) = f x := by
  let l : Y →ₗ[ℂ] Z :=
    (g.toLinearMap.ker.liftQ f.toLinearMap hker).comp
      (g.toLinearMap.quotKerEquivOfSurjective hg).symm.toLinearMap
  have hl (x : X) : l (g x) = f x := by
    change (g.toLinearMap.ker.liftQ f.toLinearMap hker)
      ((g.toLinearMap.quotKerEquivOfSurjective hg).symm (g.toLinearMap x)) = f x
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  refine ⟨⟨l, fun a => ?_⟩, hl⟩
  ext y
  obtain ⟨x, rfl⟩ := hg y
  change l (σ a (g x)) = τ a (l (g x))
  rw [← Representation.IntertwiningMap.isIntertwining _ _ g a x, hl, hl]
  exact Representation.IntertwiningMap.isIntertwining _ _ f a x

/-- An isomorphism of actual representations exhibits its target as a
subquotient of its source. -/
theorem isSubquotient_of_iso {P Q : Rep.{uV} ℂ G} (e : P ≅ Q) :
    IsSubquotient P.ρ Q.ρ :=
  IsSubquotient.of_surjective e.hom.hom fun y => ⟨e.inv.hom y, by
    change (e.inv ≫ e.hom).hom y = y
    rw [e.inv_hom_id]
    rfl⟩

/-- Every graded piece of a finite natural filtration is, at every object, an
actual subquotient of the filtered representation. -/
theorem isSubquotient_graded {F : C ⥤ Rep.{uV} ℂ G} {n : ℕ}
    (s : RepFunctorFiltration F n) (Y : C) (j : Fin n) :
    IsSubquotient (F.obj Y).ρ ((s.graded j).obj Y).ρ :=
  ⟨(s.step j.succ).obj Y,
    ((s.step j.castSucc).quotientProjection (s.step j.succ) Y).hom,
    (s.step j.castSucc).quotientProjection_surjective (s.step j.succ) Y⟩

/-- An irreducible actual subquotient of a finitely filtered representation is
an actual subquotient of one graded piece. The graded pieces need not be
irreducible. -/
theorem exists_isSubquotient_graded {F : C ⥤ Rep.{uV} ℂ G} {n : ℕ}
    (s : RepFunctorFiltration F n) (Y : C) {X : Representation ℂ G W}
    [X.IsIrreducible] (h : IsSubquotient (F.obj Y).ρ X) :
    ∃ j : Fin n, IsSubquotient ((s.graded j).obj Y).ρ X := by
  classical
  obtain ⟨U, f, hf⟩ := h
  have : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) X.asModule
  let A (i : Fin (n + 1)) : Subrepresentation (F.obj Y).ρ := (s.step i).obj Y
  let P (i : Fin (n + 1)) : Prop :=
    ∀ x : U.toSubmodule, (x : F.obj Y) ∈ A i → f x = 0
  have hzero : P 0 := by
    intro x hx
    have hx' : (x : F.obj Y) ∈ (⊥ : Subrepresentation (F.obj Y).ρ) := by
      rw [← s.zero Y]
      exact hx
    have hx0 : x = 0 := Subtype.ext hx'
    rw [hx0, map_zero]
  have hlast : ¬ P (Fin.last n) := by
    intro hP
    obtain ⟨d, hd⟩ := exists_ne (0 : W)
    obtain ⟨x, rfl⟩ := hf d
    refine hd (hP x ?_)
    change (x : F.obj Y) ∈ (s.step (Fin.last n)).obj Y
    rw [s.top Y]
    trivial
  have hstep : ∃ j : Fin n, P j.castSucc ∧ ¬ P j.succ := by
    by_contra hne
    have hnext : ∀ j : Fin n, P j.castSucc → P j.succ := by
      intro j hj
      by_contra hj'
      exact hne ⟨j, hj, hj'⟩
    exact hlast (Fin.induction hzero hnext (Fin.last n))
  obtain ⟨j, hj, hj'⟩ := hstep
  change ¬ (∀ x : U.toSubmodule, (x : F.obj Y) ∈ A j.succ → f x = 0) at hj'
  push Not at hj'
  obtain ⟨x, hx, hfx⟩ := hj'
  let X' : Subrepresentation (F.obj Y).ρ := U ⊓ A j.succ
  let iS : X'.toRepresentation.IntertwiningMap U.toRepresentation :=
    { toLinearMap :=
        { toFun := fun v => ⟨v.val, v.property.1⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }
  let iT : X'.toRepresentation.IntertwiningMap (A j.succ).toRepresentation :=
    { toLinearMap :=
        { toFun := fun v => ⟨v.val, v.property.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }
  let q : X'.toRepresentation.IntertwiningMap ((s.graded j).obj Y).ρ :=
    ((s.step j.castSucc).quotientProjection (s.step j.succ) Y).hom.comp iT
  let fX := f.comp iS
  have hker : q.toLinearMap.ker ≤ fX.toLinearMap.ker := by
    intro v hv
    have hv' : Submodule.Quotient.mk
        (p := ((s.step j.castSucc).lowerInUpper (s.step j.succ) Y).toSubmodule)
        (iT v) = 0 := hv
    have hmem : iT v ∈ ((s.step j.castSucc).lowerInUpper (s.step j.succ) Y).toSubmodule :=
      (Submodule.Quotient.mk_eq_zero _).mp hv'
    exact hj (iS v) hmem
  have hfX : Function.Surjective fX := by
    refine (Representation.IsIrreducible.surjective_or_eq_zero fX).resolve_right ?_
    intro h0
    apply hfx
    change fX ⟨x.val, x.property, hx⟩ = 0
    rw [h0]
    rfl
  let R : Subrepresentation ((s.graded j).obj Y).ρ := q.range
  let q' : X'.toRepresentation.IntertwiningMap R.toRepresentation :=
    { toLinearMap := q.toLinearMap.rangeRestrict
      isIntertwining' := by
        intro g
        ext v
        exact Representation.IntertwiningMap.isIntertwining _ _ q g v }
  have hq' : Function.Surjective q' := LinearMap.surjective_rangeRestrict _
  have hker' : q'.toLinearMap.ker ≤ fX.toLinearMap.ker := by
    change LinearMap.ker q.toLinearMap.rangeRestrict ≤ _
    rw [LinearMap.ker_rangeRestrict]
    exact hker
  obtain ⟨d, hd⟩ := exists_descend q' fX hq' hker'
  refine ⟨j, R, d, fun z => ?_⟩
  obtain ⟨v, rfl⟩ := hfX z
  exact ⟨q' v, hd v⟩

/-- Every glued piece is, at every object, an actual subquotient. -/
theorem IsGluedFrom.isSubquotient_piece {F : C ⥤ Rep.{uV} ℂ G} {n : ℕ}
    {pieces : Fin n → C ⥤ Rep.{uV} ℂ G} (h : IsGluedFrom F pieces) (Y : C)
    (i : Fin n) : IsSubquotient (F.obj Y).ρ ((pieces i).obj Y).ρ := by
  obtain ⟨e, s, hs⟩ := h
  obtain ⟨φ⟩ := hs (e.symm i)
  have hi : (pieces ∘ e) (e.symm i) = pieces i := by
    simp
  rw [hi] at φ
  exact (isSubquotient_graded s Y (e.symm i)).trans (isSubquotient_of_iso (φ.app Y))

/-- An irreducible actual subquotient of a representation glued from finitely
many pieces is an actual subquotient of one piece. -/
theorem IsGluedFrom.exists_isSubquotient_piece {F : C ⥤ Rep.{uV} ℂ G} {n : ℕ}
    {pieces : Fin n → C ⥤ Rep.{uV} ℂ G} (h : IsGluedFrom F pieces) (Y : C)
    {X : Representation ℂ G W} [X.IsIrreducible] (hX : IsSubquotient (F.obj Y).ρ X) :
    ∃ i : Fin n, IsSubquotient ((pieces i).obj Y).ρ X := by
  obtain ⟨e, s, hs⟩ := h
  obtain ⟨j, hj⟩ := exists_isSubquotient_graded s Y hX
  obtain ⟨φ⟩ := hs j
  exact ⟨e j, (isSubquotient_of_iso (φ.app Y).symm).trans hj⟩

end Graded

end Langlands.WeylBranchPieces
