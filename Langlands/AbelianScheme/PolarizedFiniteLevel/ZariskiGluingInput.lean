import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingAbelian

/-! # Gluing input from local data that agree on overlaps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {g d n : ℕ} {S T T' T'' : Scheme.{u}}

theorem Isomorphic.refl' (a : Datum P T g d n) : Isomorphic a a := ⟨PolarizedIso.refl a⟩

theorem Isomorphic.symm' {a b : Datum P T g d n} (h : Isomorphic a b) : Isomorphic b a :=
  h.elim fun e => ⟨e.symm⟩

theorem Isomorphic.trans' {a b c : Datum P T g d n} (h : Isomorphic a b) (h' : Isomorphic b c) :
    Isomorphic a c :=
  h.elim fun e => h'.elim fun e' => ⟨e.trans e'⟩

theorem Isomorphic.pullback' {a b : Datum P T g d n} (h : Isomorphic a b) (f : T' ⟶ T) :
    Isomorphic (a.pullback f) (b.pullback f) :=
  h.elim fun e => ⟨e.pullback f⟩

theorem Isomorphic.pullback_comp (a : Datum P T g d n) (f : T' ⟶ T) (f' : T'' ⟶ T') :
    Isomorphic (a.pullback (f' ≫ f)) ((a.pullback f).pullback f') :=
  ⟨a.pullbackCompIso f f'⟩

theorem Isomorphic.pullback_congr (a : Datum P T g d n) {f f' : T' ⟶ T} (h : f = f') :
    Isomorphic (a.pullback f) (a.pullback f') := by
  subst h
  exact Isomorphic.refl' _

namespace ZariskiGluing

variable {J : Type*} {U : J → S.Opens} (a : ∀ i, Datum P (U i).toScheme g d n)

/-- A chosen member of `U` containing a small open. -/
def index (W : SubOpens U) : J := W.2.choose

theorem le_index (W : SubOpens U) : W.1 ≤ U (index W) := W.2.choose_spec

/-- The datum on a small open: the restriction of the datum on the chosen member. -/
def localDatum (W : SubOpens U) : Datum P W.1.toScheme g d n :=
  (a (index W)).pullback (S.homOfLE (le_index W))

variable {a}

/-- Restrictions of two members' data to a common small open are isomorphic. -/
theorem isomorphic_restrict
    (h : ∀ i j, Isomorphic ((a i).pullback (S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)))
      ((a j).pullback (S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))))
    (V : S.Opens) {i j : J} (hi : V ≤ U i) (hj : V ≤ U j) :
    Isomorphic ((a i).pullback (S.homOfLE hi)) ((a j).pullback (S.homOfLE hj)) := by
  have hij : V ≤ U i ⊓ U j := le_inf hi hj
  have e1 : Isomorphic ((a i).pullback (S.homOfLE hi))
      (((a i).pullback (S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).pullback
        (S.homOfLE hij)) :=
    (Isomorphic.pullback_congr _ (S.homOfLE_homOfLE hij inf_le_left).symm).trans'
      (Isomorphic.pullback_comp _ _ _)
  have e2 : Isomorphic ((a j).pullback (S.homOfLE hj))
      (((a j).pullback (S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))).pullback
        (S.homOfLE hij)) :=
    (Isomorphic.pullback_congr _ (S.homOfLE_homOfLE hij inf_le_right).symm).trans'
      (Isomorphic.pullback_comp _ _ _)
  exact e1.trans' (((h i j).pullback' (S.homOfLE hij)).trans' e2.symm')

/-- The local data on two nested small opens are compatible. -/
theorem isomorphic_localDatum
    (h : ∀ i j, Isomorphic ((a i).pullback (S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)))
      ((a j).pullback (S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))))
    (W W' : SubOpens U) (hWW' : W.1 ≤ W'.1) :
    Isomorphic (localDatum a W) ((localDatum a W').pullback (S.homOfLE hWW')) := by
  have e1 : Isomorphic ((localDatum a W').pullback (S.homOfLE hWW'))
      ((a (index W')).pullback (S.homOfLE (hWW'.trans (le_index W')))) :=
    (Isomorphic.pullback_comp _ _ _).symm'.trans'
      (Isomorphic.pullback_congr _ (S.homOfLE_homOfLE hWW' (le_index W')))
  exact (isomorphic_restrict h W.1 (le_index W) (hWW'.trans (le_index W'))).trans' e1.symm'

/-- The chosen polarized isomorphisms between nested small opens. -/
def transition
    (h : ∀ i j, Isomorphic ((a i).pullback (S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)))
      ((a j).pullback (S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))))
    (W W' : SubOpens U) (hWW' : W.1 ≤ W'.1) :
    PolarizedIso (localDatum a W) ((localDatum a W').pullback (S.homOfLE hWW')) :=
  Classical.choice (isomorphic_localDatum h W W' hWW')

end ZariskiGluing

end Langlands.AbelianScheme.PolarizedFiniteLevel
