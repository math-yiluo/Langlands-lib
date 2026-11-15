import Langlands.Representation.Classification.LeftCuspidalDerivative.Uniqueness
import Langlands.Representation.Aubert.GradedInductionAssociativityProof
import Langlands.Representation.Classification.BernsteinBinaryRankZero

/-!
# Iterated products with a supercuspidal representation as binary products

For a supercuspidal `A` of `GL_d` (`d > 0`) and `K ≥ 1`:

* `nonempty_powerProduct_iso`: `A^K × Y = A × (A × ⋯ × (A × Y))` is isomorphic to the binary
  product `(A × ⋯ × A) × Y` of the cuspidal power `cuspidalPower` with `Y`, after rank
  transport, for `Y` of positive rank;
* `nonempty_powerProduct_rankZero_iso`: for an irreducible `S` of `GL_0`, `A^K × S` is
  isomorphic to the cuspidal power, after rank transport.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

section CastRank

variable {F}

/-- Rank transport carries isomorphisms to isomorphisms. -/
theorem nonempty_castRank_iso {r s : ℕ} (h : r = s)
    {X X' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)}
    (e : letI := T.topology; X ≅ X') :
    letI := T.topology; Nonempty (T.castRank h X ≅ T.castRank h X') := by
  subst h
  exact ⟨e⟩

/-- A rank transport of the left factor of a binary product moves outside. -/
theorem binaryProduct_castRank_left {a a' m : ℕ} (h : a' = a) (h' : a' + m = a + m)
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a' F.Carrier))
    (Y : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)) :
    letI := T.topology
    (T.binaryNormalizedProductFunctor.{uF, uV} a m).obj (T.castRank h X, Y) =
      T.castRank h' ((T.binaryNormalizedProductFunctor.{uF, uV} a' m).obj (X, Y)) := by
  subst h
  rfl

/-- A rank transport of the right factor of a binary product moves outside. -/
theorem binaryProduct_castRank_right {d m m' : ℕ} (h : m' = m) (h' : d + m' = d + m)
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear d F.Carrier))
    (Y : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear m' F.Carrier)) :
    letI := T.topology
    (T.binaryNormalizedProductFunctor.{uF, uV} d m).obj (X, T.castRank h Y) =
      T.castRank h' ((T.binaryNormalizedProductFunctor.{uF, uV} d m').obj (X, Y)) := by
  subst h
  rfl

/-- An equivalence with a representation restricted along the rank reindexing gives an
isomorphism with a rank transport. -/
theorem nonempty_iso_castRank_of_equiv_comp {n n' : ℕ} (h : n = n')
    (L : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (R : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n' F.Carrier))
    (e : letI := T.topology; L.representation.Equiv (R.representation.comp
      (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).toMonoidHom)) :
    letI := T.topology; Nonempty (R ≅ T.castRank h L) := by
  let := T.topology
  subst h
  have hc : R.representation.comp
      (GeneralLinear.reindex (R := F.Carrier) (finCongr (rfl : n = n))).toMonoidHom =
      R.representation := by
    rw [GeneralLinear.reindex_finCongr_rfl]
    exact MonoidHom.ext fun _ => rfl
  exact ⟨(SmoothRep.mkIso (e.trans (equivOfRepresentationEq hc))).symm⟩

/-- Associativity of binary products of positive ranks, as an isomorphism after rank
transport (`Aubert.GradedAssociativityProof.binaryAssocEquiv`). -/
theorem nonempty_binaryAssocIso {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier)) :
    letI := T.topology
    Nonempty ((T.binaryNormalizedProductFunctor.{uF, max uF uV} a (b + c)).obj
        (X, (T.binaryNormalizedProductFunctor.{uF, max uF uV} b c).obj (Y, Z)) ≅
      T.castRank (Nat.add_assoc a b c)
        ((T.binaryNormalizedProductFunctor.{uF, max uF uV} (a + b) c).obj
          ((T.binaryNormalizedProductFunctor.{uF, max uF uV} a b).obj (X, Y), Z))) :=
  nonempty_iso_castRank_of_equiv_comp T (Nat.add_assoc a b c) _ _
    (Aubert.GradedAssociativityProof.binaryAssocEquiv.{uF, uV} F T ha hb hc X Y Z)

/-- For an irreducible `S` of `GL_0`, the binary product `X × S` is `X`, after rank
transport. -/
theorem nonempty_binaryProduct_rankZero_iso {n : ℕ}
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (S : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
    (hS : letI := T.topology; S.IsIrreducible) :
    letI := T.topology
    Nonempty ((T.binaryNormalizedProductFunctor.{uF, max uF uV} n 0).obj (X, S) ≅
      T.castRank (Nat.add_zero n).symm X) := by
  let := T.topology
  let e0 := (T.binaryNormalizedProductFunctor.{uF, max uF uV} n 0).mapIso
    (Iso.prod (Iso.refl X) (rankZeroIrreducibleUnitIso.{uF, max uF uV} F T S hS))
  let e1 := T.binaryProductRightUnitEquiv.{uF, max uF uV} X
  let e2 := (BinaryTensor.liftEquiv.{uF, max uF uV, uF}
    (X.representation.comp
      (GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.add_zero n))).toMonoidHom)).symm
  have hc : X.representation.comp
      (GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.add_zero n))).toMonoidHom =
      X.representation :=
    MonoidHom.ext fun g =>
      congrArg X.representation (Units.ext (Matrix.ext fun _ _ => rfl))
  exact ⟨e0 ≪≫ SmoothRep.mkIso (B := T.castRank (Nat.add_zero n).symm X)
    ((e1.trans e2).trans (equivOfRepresentationEq hc))⟩

end CastRank

section Power

variable {d : ℕ} (hd : 0 < d)
  (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))

theorem sum_cuspidalDatumOf_rank (K : ℕ) :
    ∑ _i : Fin K, (cuspidalDatumOf T hd A).rank = K * d := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rfl

/-- **`A^(K+1) × Y` as a binary product.** For `Y` of positive rank, the iterated product
`A × (A × ⋯ × (A × Y))` with `K + 1` factors `A` is isomorphic to the binary product of the
cuspidal power `A × ⋯ × A` with `Y`, after rank transport. -/
theorem nonempty_powerProduct_iso {m : ℕ} (hm : 0 < m)
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (K : ℕ) :
    ∀ {a : ℕ} (ha : ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank = a)
      (h : a + m = powerRank d (K + 1) m),
      letI := T.topology
      Nonempty (powerProduct F T A (K + 1) Y ≅
        T.castRank h ((T.binaryNormalizedProductFunctor.{uF, max uF uV} a m).obj
          (cuspidalPower T hd A (K + 1) ha, Y))) := by
  let := T.topology
  induction K with
  | zero =>
    intro a ha h
    have hn : d = a := by
      rw [← ha, Fin.sum_univ_one]
      rfl
    let e1 : cuspidalPower T hd A 1 ha ≅ T.castRank hn A.obj :=
      SmoothRep.mkIso (cuspidalPowerOneEquiv T hd A ha hn)
    have h' : d + m = a + m := by omega
    let e2 := (T.binaryNormalizedProductFunctor.{uF, max uF uV} a m).mapIso
        (Iso.prod e1 (Iso.refl Y)) ≪≫
      eqToIso (binaryProduct_castRank_left T hn h' A.obj Y)
    obtain ⟨e3⟩ := nonempty_castRank_iso T h e2
    exact ⟨(e3 ≪≫ eqToIso (castRank_trans T h' h _)).symm⟩
  | succ K ih =>
    intro a ha h
    have hpos : 0 < ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank :=
      Finset.sum_pos (fun _ _ => hd) ⟨0, Finset.mem_univ _⟩
    have hP : (∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank) + m =
        powerRank d (K + 1) m := by
      rw [sum_cuspidalDatumOf_rank, powerRank_eq]
      ring
    have hn : d + ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank = a := by
      rw [← ha, Fin.sum_univ_succ (n := K + 1)]
      rfl
    obtain ⟨e0⟩ := ih rfl hP
    -- `A × (A^(K+1) × Y)`
    let e1 := (T.binaryNormalizedProductFunctor.{uF, max uF uV} d
        (powerRank d (K + 1) m)).mapIso (Iso.prod (Iso.refl A.obj) e0)
    have h2 : d + ((∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank) + m) =
        d + powerRank d (K + 1) m := by omega
    let e2 := eqToIso (binaryProduct_castRank_right T hP h2 A.obj
      ((T.binaryNormalizedProductFunctor.{uF, max uF uV} _ m).obj
        (cuspidalPower T hd A (K + 1) rfl, Y)))
    obtain ⟨e3⟩ := nonempty_binaryAssocIso T hd hpos hm A.obj
      (cuspidalPower T hd A (K + 1) rfl) Y
    obtain ⟨e3'⟩ := nonempty_castRank_iso T h2 e3
    -- `A^(K+2) ≅ A × A^(K+1)`
    obtain ⟨e4⟩ := nonempty_cuspidalPowerSuccIso T hd A K rfl ha hn
    have h5 : d + (∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank) + m = a + m := by omega
    let e5 := (T.binaryNormalizedProductFunctor.{uF, max uF uV} a m).mapIso
        (Iso.prod e4 (Iso.refl Y)) ≪≫
      eqToIso (binaryProduct_castRank_left T hn h5 _ Y)
    obtain ⟨e6⟩ := nonempty_castRank_iso T h e5
    exact ⟨e1 ≪≫ e2 ≪≫ e3' ≪≫ eqToIso (castRank_trans T _ h2 _) ≪≫
      (e6 ≪≫ eqToIso (castRank_trans T h5 h _)).symm⟩

/-- **`A^(K+1) × S` for `S` on `GL_0`.** For an irreducible `S` of `GL_0`, the iterated
product with `K + 1` factors `A` is isomorphic to the cuspidal power, after rank
transport. -/
theorem nonempty_powerProduct_rankZero_iso
    (S : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
    (hS : letI := T.topology; S.IsIrreducible) (K : ℕ) :
    ∀ {a : ℕ} (ha : ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank = a)
      (h : a = powerRank d (K + 1) 0),
      letI := T.topology
      Nonempty (powerProduct F T A (K + 1) S ≅ T.castRank h (cuspidalPower T hd A (K + 1) ha)) := by
  let := T.topology
  induction K with
  | zero =>
    intro a ha h
    have hn : d = a := by
      rw [← ha, Fin.sum_univ_one]
      rfl
    obtain ⟨e0⟩ := nonempty_binaryProduct_rankZero_iso T A.obj S hS
    let e1 : cuspidalPower T hd A 1 ha ≅ T.castRank hn A.obj :=
      SmoothRep.mkIso (cuspidalPowerOneEquiv T hd A ha hn)
    obtain ⟨e2⟩ := nonempty_castRank_iso T h e1
    exact ⟨e0 ≪≫ (e2 ≪≫ eqToIso (castRank_trans T hn h _)).symm⟩
  | succ K ih =>
    intro a ha h
    have hP : ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank = powerRank d (K + 1) 0 := by
      rw [sum_cuspidalDatumOf_rank, powerRank_eq]
      ring
    have hn : d + ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank = a := by
      rw [← ha, Fin.sum_univ_succ (n := K + 1)]
      rfl
    obtain ⟨e0⟩ := ih rfl hP
    let e1 := (T.binaryNormalizedProductFunctor.{uF, max uF uV} d
        (powerRank d (K + 1) 0)).mapIso (Iso.prod (Iso.refl A.obj) e0)
    have h2 : d + ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank =
        d + powerRank d (K + 1) 0 := by omega
    let e2 := eqToIso (binaryProduct_castRank_right T hP h2 A.obj
      (cuspidalPower T hd A (K + 1) rfl))
    obtain ⟨e4⟩ := nonempty_cuspidalPowerSuccIso T hd A K rfl ha hn
    obtain ⟨e5⟩ := nonempty_castRank_iso T hn.symm e4
    -- `castRank hn.symm A^(K+2) ≅ A × A^(K+1)`
    let e6 := e5 ≪≫ eqToIso (castRank_trans T hn hn.symm _)
    obtain ⟨e7⟩ := nonempty_castRank_iso T h2 e6
    exact ⟨e1 ≪≫ e2 ≪≫ e7.symm ≪≫ eqToIso (castRank_trans T hn.symm h2 _)⟩

end Power

end Langlands.Classification.LeftCuspidalDerivative
