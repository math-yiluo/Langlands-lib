import Langlands.GroupScheme.Descent.Data

/-! # Descent coherence from unique pullback lifts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Descent

variable {B S T U : Scheme.{u}} {C H : GroupScheme S}

/-- Every isomorphism between two pullbacks of the target has a unique
homomorphism lift between the corresponding pullbacks of the supplied source.
This is a property on actual schemes, including nonfield overlap schemes. -/
def HasUniquePullbackIsoLifts (π : C ⟶ H) : Prop :=
  ∀ (T : Scheme.{u}) (f g : T ⟶ S)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H),
    ∃! a : (baseChange f).obj C ⟶ (baseChange g).obj C,
      a ≫ (baseChange g).map π = (baseChange f).map π ≫ e.hom

namespace HasUniquePullbackIsoLifts

variable {π : C ⟶ H} (hπ : HasUniquePullbackIsoLifts π)

/-- The homomorphism promised by unique lifting. -/
def lift (f g : T ⟶ S) (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    (baseChange f).obj C ⟶ (baseChange g).obj C :=
  (hπ T f g e).choose

@[reassoc]
theorem lift_fac (f g : T ⟶ S)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    hπ.lift f g e ≫ (baseChange g).map π = (baseChange f).map π ≫ e.hom :=
  (hπ T f g e).choose_spec.1

/-- Compatibility with the target isomorphism determines a lift. -/
theorem lift_unique (f g : T ⟶ S)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H)
    (a : (baseChange f).obj C ⟶ (baseChange g).obj C)
    (ha : a ≫ (baseChange g).map π = (baseChange f).map π ≫ e.hom) :
    a = hπ.lift f g e :=
  (hπ T f g e).choose_spec.2 a ha

include hπ in
/-- Two lifts of the same target isomorphism coincide. -/
theorem hom_ext (f g : T ⟶ S)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H)
    {a b : (baseChange f).obj C ⟶ (baseChange g).obj C}
    (ha : a ≫ (baseChange g).map π = (baseChange f).map π ≫ e.hom)
    (hb : b ≫ (baseChange g).map π = (baseChange f).map π ≫ e.hom) :
    a = b :=
  (hπ.lift_unique f g e a ha).trans (hπ.lift_unique f g e b hb).symm

@[simp]
theorem lift_refl (f : T ⟶ S) :
    hπ.lift f f (Iso.refl _) = 𝟙 _ :=
  (hπ.lift_unique f f (Iso.refl _) (𝟙 _) (by simp)).symm

/-- Lifts preserve composition, by uniqueness over the composite isomorphism. -/
theorem lift_trans (f g h : T ⟶ S)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H)
    (d : (baseChange g).obj H ≅ (baseChange h).obj H) :
    hπ.lift f h (e ≪≫ d) = hπ.lift f g e ≫ hπ.lift g h d := by
  symm
  apply hπ.lift_unique f h (e ≪≫ d)
  simp only [Category.assoc, lift_fac, lift_fac_assoc, Iso.trans_hom]

/-- The unique lift of a target isomorphism is an actual source isomorphism. -/
def liftIso (f g : T ⟶ S)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    (baseChange f).obj C ≅ (baseChange g).obj C where
  hom := hπ.lift f g e
  inv := hπ.lift g f e.symm
  hom_inv_id := by
    rw [← lift_trans]
    simp
  inv_hom_id := by
    rw [← lift_trans]
    simp

@[simp]
theorem liftIso_hom (f g : T ⟶ S)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    (hπ.liftIso f g e).hom = hπ.lift f g e := rfl

/-- The lift commutes with actual further pullback, including all endpoint
comparisons. -/
theorem pullHom_lift (q : U ⟶ T) {f g : T ⟶ S} {r s : U ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    pullHom q hf hg (hπ.lift f g e) =
      hπ.lift r s (pullIso q hf hg e) := by
  apply hπ.lift_unique r s (pullIso q hf hg e)
  have h := congrArg (pullHom q hf hg) (hπ.lift_fac f g e)
  simpa only [pullHom_comp q hf hg hg, pullHom_comp q hf hf hg,
    pullHom_map, pullIso_hom] using h

/-- Isomorphism lifts commute with actual further pullback. -/
theorem pullIso_liftIso (q : U ⟶ T) {f g : T ⟶ S} {r s : U ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    pullIso q hf hg (hπ.liftIso f g e) =
      hπ.liftIso r s (pullIso q hf hg e) := by
  apply Iso.ext
  exact hπ.pullHom_lift q hf hg e

end HasUniquePullbackIsoLifts

variable {p : S ⟶ B} {π : C ⟶ H}

/-- Unique lifts transfer actual descent data from the target to the source.
Both the overlap isomorphism and the cocycle are constructed. -/
def Datum.lift (D : Datum p H) (hπ : HasUniquePullbackIsoLifts π) : Datum p C where
  overlap := hπ.liftIso (fst p) (snd p) D.overlap
  cocycle := by
    change
      (pullIso (p12 p) rfl rfl (hπ.liftIso (fst p) (snd p) D.overlap)).hom ≫
        (pullIso (p23 p) (p23_fst p) rfl
          (hπ.liftIso (fst p) (snd p) D.overlap)).hom =
        (pullIso (p13 p) (p13_fst p) (p13_snd p)
          (hπ.liftIso (fst p) (snd p) D.overlap)).hom
    rw [hπ.pullIso_liftIso, hπ.pullIso_liftIso, hπ.pullIso_liftIso]
    change hπ.lift (p1 p) (p2 p) (iso12 D.overlap) ≫
        hπ.lift (p2 p) (p3 p) (iso23 D.overlap) =
      hπ.lift (p1 p) (p3 p) (iso13 D.overlap)
    rw [← hπ.lift_trans]
    have hc : iso12 D.overlap ≪≫ iso23 D.overlap = iso13 D.overlap :=
      Iso.ext D.cocycle
    rw [hc]

/-- The original cover map respects the constructed source datum. -/
theorem Datum.compatible_lift (D : Datum p H) (hπ : HasUniquePullbackIsoLifts π) :
    Compatible (D.lift hπ) D π :=
  (hπ.lift_fac (fst p) (snd p) D.overlap).symm

/-- Every compatible source datum equals the one constructed by unique lifting. -/
theorem Datum.lift_unique (D : Datum p H) (hπ : HasUniquePullbackIsoLifts π)
    (E : Datum p C) (hE : Compatible E D π) : E = D.lift hπ := by
  apply Datum.ext
  apply Iso.ext
  exact hπ.lift_unique (fst p) (snd p) D.overlap E.overlap.hom hE.symm

end Langlands.GroupScheme.Descent
