import Langlands.Geometry.FormalGroup.OrderRationalMorphism

/-! # Inverse and square calculus for actual order-linear quasi-isogenies -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.OrderAction.QuasiIsogeny

variable {O : Type u} [CommRing O] [IsDomain O]
variable {D : Type v} [Ring D] [Algebra O D]
variable {R : Type w} [CommRing R] [Algebra O R]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ υ ω η θ : Type}
  [Finite σ] [Finite τ] [Finite υ] [Finite ω] [Finite η] [Finite θ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
  {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}
  {S : ModuleLaw O R η} {T : ModuleLaw O R θ}
variable {E : OrderAction D M} {E' : OrderAction D N}
  {E'' : OrderAction D P} {E''' : OrderAction D Q}
  {E₄ : OrderAction D S} {E₅ : OrderAction D T}

@[simp]
theorem refl_trans (f : QuasiIsogeny F E E') : (refl E).trans f = f := by
  apply ext
  exact RationalHom.comp_id f.hom

@[simp]
theorem trans_refl (f : QuasiIsogeny F E E') : f.trans (refl E') = f := by
  apply ext
  exact RationalHom.id_comp f.hom

theorem trans_assoc (f : QuasiIsogeny F E E') (g : QuasiIsogeny F E' E'')
    (h : QuasiIsogeny F E'' E''') :
    (f.trans g).trans h = f.trans (g.trans h) := by
  apply ext
  exact (RationalHom.comp_assoc h.hom g.hom f.hom).symm

@[simp]
theorem symm_symm (f : QuasiIsogeny F E E') : f.symm.symm = f := rfl

@[simp]
theorem symm_refl (E : OrderAction D M) : (refl (F := F) E).symm = refl E := rfl

@[simp]
theorem self_trans_symm (f : QuasiIsogeny F E E') :
    f.trans f.symm = refl E := by
  apply ext
  exact f.inv_hom

@[simp]
theorem symm_trans_self (f : QuasiIsogeny F E E') :
    f.symm.trans f = refl E' := by
  apply ext
  exact f.hom_inv

theorem symm_trans (f : QuasiIsogeny F E E') (g : QuasiIsogeny F E' E'') :
    (f.trans g).symm = g.symm.trans f.symm := rfl

theorem trans_right_cancel (f g : QuasiIsogeny F E E') (h : QuasiIsogeny F E' E'')
    (e : f.trans h = g.trans h) : f = g := by
  have t := congrArg (fun k => k.trans h.symm) e
  simpa only [trans_assoc, self_trans_symm, trans_refl] using t

theorem trans_left_cancel (f : QuasiIsogeny F E E') (g h : QuasiIsogeny F E' E'')
    (e : f.trans g = f.trans h) : g = h := by
  have t := congrArg (fun k => f.symm.trans k) e
  simpa only [← trans_assoc, symm_trans_self, refl_trans] using t

/-- Reverse the two vertical quasi-isogenies in an actual commuting square. -/
theorem square_reverse
    (f : QuasiIsogeny F E E') (g : QuasiIsogeny F E' E'')
    (a : QuasiIsogeny F E E''') (b : QuasiIsogeny F E''' E'')
    (h : f.trans g = a.trans b) :
    b.trans g.symm = a.symm.trans f := by
  calc
    b.trans g.symm = (refl E''').trans (b.trans g.symm) := (refl_trans _).symm
    _ = (a.symm.trans a).trans (b.trans g.symm) := by rw [symm_trans_self]
    _ = a.symm.trans ((a.trans b).trans g.symm) := by
      simp only [trans_assoc]
    _ = a.symm.trans ((f.trans g).trans g.symm) := by rw [← h]
    _ = a.symm.trans f := by rw [trans_assoc, self_trans_symm, trans_refl]

/-- Paste two actual rational squares along their shared framing. -/
theorem square_paste
    (f : QuasiIsogeny F E E') (g : QuasiIsogeny F E' E'')
    (a : QuasiIsogeny F E E''') (b : QuasiIsogeny F E''' E'')
    (g' : QuasiIsogeny F E'' E₄) (a' : QuasiIsogeny F E''' E₅)
    (c : QuasiIsogeny F E₅ E₄)
    (h : f.trans g = a.trans b) (h' : b.trans g' = a'.trans c) :
    f.trans (g.trans g') = (a.trans a').trans c := by
  calc
    f.trans (g.trans g') = (f.trans g).trans g' := (trans_assoc _ _ _).symm
    _ = (a.trans b).trans g' := by rw [h]
    _ = a.trans (b.trans g') := trans_assoc _ _ _
    _ = a.trans (a'.trans c) := by rw [h']
    _ = (a.trans a').trans c := (trans_assoc _ _ _).symm

/-- Four actual full-order quasi-isogenies with their actual commuting-square equation. -/
structure CommutingSquare (E : OrderAction D M) (E' : OrderAction D N)
    (E'' : OrderAction D P) (E''' : OrderAction D Q) where
  top : QuasiIsogeny F E E'
  right : QuasiIsogeny F E' E''
  left : QuasiIsogeny F E E'''
  bottom : QuasiIsogeny F E''' E''
  commutes : top.trans right = left.trans bottom

namespace CommutingSquare

/-- Reverse the two vertical actual maps of the supplied square. -/
def reverse (s : CommutingSquare (F := F) E E' E'' E''') :
    CommutingSquare (F := F) E''' E'' E' E where
  top := s.bottom
  right := s.right.symm
  left := s.left.symm
  bottom := s.top
  commutes := square_reverse s.top s.right s.left s.bottom s.commutes

/-- Paste the supplied squares along their shared actual horizontal map. -/
def paste (s : CommutingSquare (F := F) E E' E'' E''')
    (t : CommutingSquare (F := F) E''' E'' E₄ E₅) (h : s.bottom = t.top) :
    CommutingSquare (F := F) E E' E₄ E₅ where
  top := s.top
  right := s.right.trans t.right
  left := s.left.trans t.left
  bottom := t.bottom
  commutes := square_paste s.top s.right s.left s.bottom t.right t.left t.bottom
    s.commutes ((congrArg (fun f => f.trans t.right) h).trans t.commutes)

end CommutingSquare

end Langlands.FormalGroup.ModuleLaw.OrderAction.QuasiIsogeny
