/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Transport of spectral sequences along fully faithful exact functors

Let `G : A ⥤ B` be a fully faithful exact functor between abelian categories whose essential
image is closed under subobjects of objects of the form `G.obj Y`. If a first quadrant
cohomological spectral sequence `E'` in `B` has its `E₂`-page in the essential image of `G` and
abuts to `G.obj (H n)`, then it comes from a spectral sequence in `A` abutting to `H n`.

The main application is to `AddCommGrpCat.uliftFunctor : AddCommGrpCat.{w} ⥤
AddCommGrpCat.{max w v}`, which allows to bring spectral sequences constructed in a larger
universe back down to the universe of the groups involved.

## Main statements

- `CategoryTheory.Functor.essImage_homology`: the homology of a complex whose objects lie in the
  essential image of a fully faithful exact functor lies in the essential image.
- `CategoryTheory.SpectralSequence.exists_of_fullyFaithful`: transport of a first quadrant
  spectral sequence together with its abutment along a fully faithful exact functor.
- `AddCommGrpCat.uliftFunctor_essImage_of_mono`: a subgroup of a universe lifted group is in the
  essential image of `AddCommGrpCat.uliftFunctor`.
- `CategoryTheory.SpectralSequence.exists_of_uliftFunctor`: universe lowering for first quadrant
  spectral sequences of abelian groups.
-/

@[expose] public section

universe w v v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

namespace Functor

section Preadditive

variable [Preadditive A] [Preadditive B] (G : A ⥤ B) [G.Full] [G.Faithful] [G.Additive]
  {ι : Type*} {c : ComplexShape ι}

/-- A homological complex in `B` whose objects lie in the essential image of a fully faithful
additive functor `G : A ⥤ B`, lifted to a homological complex in `A`. -/
@[simps]
noncomputable def liftHomologicalComplex (K : HomologicalComplex B c)
    (hK : ∀ i, G.essImage (K.X i)) : HomologicalComplex A c where
  X i := (hK i).witness
  d i j := G.preimage ((hK i).getIso.hom ≫ K.d i j ≫ (hK j).getIso.inv)
  shape i j h := G.map_injective (by simp [K.shape i j h])
  d_comp_d' i j k _ _ := G.map_injective (by simp)

/-- The image under `G` of `G.liftHomologicalComplex K hK` is isomorphic to `K`. -/
noncomputable def mapLiftHomologicalComplexIso (K : HomologicalComplex B c)
    (hK : ∀ i, G.essImage (K.X i)) :
    (G.mapHomologicalComplex c).obj (G.liftHomologicalComplex K hK) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ (hK i).getIso) (by simp)

end Preadditive

section Abelian

variable [Abelian A] [Abelian B] (G : A ⥤ B) [G.Full] [G.Faithful] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] {ι : Type*} {c : ComplexShape ι}

/-- For a fully faithful exact functor `G`, the homology of the lift of a complex `K` is
identified with the homology of `K` after applying `G`. -/
noncomputable def homologyLiftHomologicalComplexIso (K : HomologicalComplex B c)
    (hK : ∀ i, G.essImage (K.X i)) (i : ι) :
    G.obj ((G.liftHomologicalComplex K hK).homology i) ≅ K.homology i :=
  (((G.liftHomologicalComplex K hK).sc i).mapHomologyIso G).symm ≪≫
    HomologicalComplex.homologyMapIso (G.mapLiftHomologicalComplexIso K hK) i

/-- The homology of a complex whose objects lie in the essential image of a fully faithful exact
functor lies in the essential image. -/
lemma essImage_homology (K : HomologicalComplex B c) (hK : ∀ i, G.essImage (K.X i)) (i : ι) :
    G.essImage (K.homology i) :=
  ⟨_, ⟨G.homologyLiftHomologicalComplexIso K hK i⟩⟩

end Abelian

section Subobject

variable {G : A ⥤ B}

/-- An object of `B` which is a subobject of `G.obj Y`, lifted to `A` when the essential image
of `G` is closed under such subobjects. -/
noncomputable def preimageSubobjectIso
    (hG : ∀ {Y : A} {Z : B} (f : Z ⟶ G.obj Y), Mono f → G.essImage Z) {Y : A}
    (S : Subobject (G.obj Y)) : G.obj (hG S.arrow inferInstance).witness ≅ (S : B) :=
  (hG S.arrow inferInstance).getIso

/-- The subobject of `Y` corresponding to a subobject of `G.obj Y`, when the essential image of
`G` is closed under subobjects. -/
noncomputable def preimageSubobjectArrow [G.Full]
    (hG : ∀ {Y : A} {Z : B} (f : Z ⟶ G.obj Y), Mono f → G.essImage Z) {Y : A}
    (S : Subobject (G.obj Y)) : (hG S.arrow inferInstance).witness ⟶ Y :=
  G.preimage ((preimageSubobjectIso hG S).hom ≫ S.arrow)

@[simp]
lemma map_preimageSubobjectArrow [G.Full]
    (hG : ∀ {Y : A} {Z : B} (f : Z ⟶ G.obj Y), Mono f → G.essImage Z) {Y : A}
    (S : Subobject (G.obj Y)) :
    G.map (preimageSubobjectArrow hG S) = (preimageSubobjectIso hG S).hom ≫ S.arrow :=
  G.map_preimage _

instance [G.Full] [G.Faithful]
    (hG : ∀ {Y : A} {Z : B} (f : Z ⟶ G.obj Y), Mono f → G.essImage Z) {Y : A}
    (S : Subobject (G.obj Y)) : Mono (preimageSubobjectArrow hG S) :=
  G.mono_of_mono_map (by rw [map_preimageSubobjectArrow]; infer_instance)

end Subobject

end Functor

namespace SpectralSequence

variable [Abelian A] [Abelian B] (G : A ⥤ B) [G.Full] [G.Faithful] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-- If the first page of a spectral sequence lies in the essential image of a fully faithful
exact functor, so do all the pages. -/
lemma essImage_page (E' : SpectralSequence B c r₀) (h : ∀ pq, G.essImage ((E'.page r₀).X pq))
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ) : G.essImage ((E'.page r).X pq) := by
  induction r, hr using Int.leInduction generalizing pq with
  | base => exact h pq
  | succ r hr ih =>
    exact Functor.essImage.ofIso (E'.iso r (r + 1) pq)
      (G.essImage_homology (E'.page r) ih pq)

/-- A spectral sequence in `B` whose pages lie in the essential image of a fully faithful exact
functor `G : A ⥤ B`, lifted to a spectral sequence in `A`. -/
@[simps page]
noncomputable def lift (E' : SpectralSequence B c r₀)
    (h : ∀ (r : ℤ) (hr : r₀ ≤ r) (pq : κ), G.essImage ((E'.page r).X pq)) :
    SpectralSequence A c r₀ where
  page r hr := G.liftHomologicalComplex (E'.page r) (h r hr)
  iso r r' pq hrr' hr := G.preimageIso
    (G.homologyLiftHomologicalComplexIso (E'.page r) (h r hr) pq ≪≫ E'.iso r r' pq ≪≫
      (h r' (by lia) pq).getIso.symm)

/-- The objects of the pages of `SpectralSequence.lift G E' h` are sent by `G` to those
of `E'`. -/
noncomputable def liftPageXIso (E' : SpectralSequence B c r₀)
    (h : ∀ (r : ℤ) (hr : r₀ ≤ r) (pq : κ), G.essImage ((E'.page r).X pq))
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    G.obj (((lift G E' h).page r).X pq) ≅ (E'.page r).X pq :=
  (h r hr pq).getIso

section Abutment

variable {G}


/-- Transport of an abutment along `G`. -/
noncomputable def liftAbutment
    (hG : ∀ {Y : A} {Z : B} (f : Z ⟶ G.obj Y), Mono f → G.essImage Z)
    (E' : E₂CohomologicalSpectralSequenceNat B)
    (h : ∀ (r : ℤ) (hr : 2 ≤ r) (pq : ℕ × ℕ), G.essImage ((E'.page r).X pq))
    (H : ℕ → A)
    (A' : E'.Abutment fun n ↦ G.obj (H n)) : (lift G E' h).Abutment H where
  filtration n p := Subobject.mk (Functor.preimageSubobjectArrow hG (A'.filtration n p))
  filtration_succ_le n p := by
    refine Subobject.mk_le_mk_of_comm (G.preimage
      ((Functor.preimageSubobjectIso hG (A'.filtration n (p + 1))).hom ≫
        Subobject.ofLE _ _ (A'.filtration_succ_le n p) ≫
          (Functor.preimageSubobjectIso hG (A'.filtration n p)).inv)) ?_
    exact G.map_injective (by simp)
  filtration_zero n := by
    have : IsIso (A'.filtration n 0).arrow := by rw [A'.filtration_zero]; infer_instance
    have : IsIso (G.map (Functor.preimageSubobjectArrow hG (A'.filtration n 0))) := by
      rw [Functor.map_preimageSubobjectArrow]; infer_instance
    have := isIso_of_fully_faithful G (Functor.preimageSubobjectArrow hG (A'.filtration n 0))
    exact Subobject.mk_eq_top_of_isIso _
  filtration_succ_self n := by
    have : (A'.filtration n (n + 1)).arrow = 0 := by
      rw [A'.filtration_succ_self]; exact Subobject.bot_arrow
    rw [Subobject.mk_eq_bot_iff_zero]
    exact G.map_injective (by simp [this])
  nonempty_gradedIso n p q hpq := by
    obtain ⟨i⟩ := A'.nonempty_gradedIso n p q hpq
    refine ⟨G.preimageIso (PreservesCokernel.iso G _ ≪≫ cokernel.mapIso _ _
      (G.mapIso (Subobject.underlyingIso _) ≪≫ Functor.preimageSubobjectIso hG _)
      (G.mapIso (Subobject.underlyingIso _) ≪≫ Functor.preimageSubobjectIso hG _) ?_ ≪≫
      i ≪≫ (h _ (by lia) _).getIso.symm)⟩
    rw [← cancel_mono (A'.filtration n p).arrow]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Subobject.ofLE_arrow]
    rw [← Functor.map_preimageSubobjectArrow, ← Functor.map_preimageSubobjectArrow]
    simp only [← G.map_comp, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]

end Abutment

/-- **Transport of spectral sequences.** Let `G : A ⥤ B` be a fully faithful exact functor
between abelian categories such that every subobject of an object `G.obj Y` lies in the
essential image of `G`. A first quadrant cohomological spectral sequence in `B` whose `E₂`-page
lies in the essential image of `G` and which abuts to `G.obj (H n)` comes from a spectral
sequence in `A` abutting to `H n`. -/
theorem exists_of_fullyFaithful
    (hG : ∀ {Y : A} {Z : B} (f : Z ⟶ G.obj Y), Mono f → G.essImage Z)
    (E' : E₂CohomologicalSpectralSequenceNat B) (H : ℕ → A)
    (h₂ : ∀ pq, G.essImage ((E'.page 2).X pq)) (hE' : E'.AbutsTo fun n ↦ G.obj (H n)) :
    ∃ E : E₂CohomologicalSpectralSequenceNat A,
      (∀ pq, Nonempty (G.obj ((E.page 2).X pq) ≅ (E'.page 2).X pq)) ∧ E.AbutsTo H :=
  ⟨lift G E' (essImage_page G E' h₂), fun pq ↦ ⟨liftPageXIso G E' _ 2 le_rfl pq⟩,
    ⟨liftAbutment hG E' _ H hE'.some⟩⟩

end SpectralSequence

end CategoryTheory

open CategoryTheory

/-- An abelian group with an injective morphism to a universe lifted abelian group is in the
essential image of `AddCommGrpCat.uliftFunctor`. -/
lemma AddCommGrpCat.uliftFunctor_essImage_of_mono {Y : AddCommGrpCat.{w}}
    {Z : AddCommGrpCat.{max w v}} (f : Z ⟶ AddCommGrpCat.uliftFunctor.{v}.obj Y) (hf : Mono f) :
    AddCommGrpCat.uliftFunctor.{v}.essImage Z := by
  have hinj : Function.Injective f := (AddCommGrpCat.mono_iff_injective f).1 hf
  have : Small.{w} Z :=
    small_of_injective (f := Equiv.ulift ∘ f) (Equiv.ulift.injective.comp hinj)
  exact ⟨AddCommGrpCat.of (Shrink.{w} Z),
    ⟨(AddEquiv.ulift.trans Shrink.addEquiv).toAddCommGrpIso⟩⟩

/-- **Universe lowering for spectral sequences of abelian groups.** A first quadrant
cohomological spectral sequence of abelian groups in `AddCommGrpCat.{max w v}` whose `E₂`-page
consists of `w`-small groups and which abuts to universe lifts of groups `H n` in
`AddCommGrpCat.{w}` comes from a spectral sequence in `AddCommGrpCat.{w}` abutting to `H`. -/
theorem CategoryTheory.SpectralSequence.exists_of_uliftFunctor
    (E' : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{max w v})
    (H : ℕ → AddCommGrpCat.{w})
    (h₂ : ∀ pq, AddCommGrpCat.uliftFunctor.{v}.essImage ((E'.page 2).X pq))
    (hE' : E'.AbutsTo fun n ↦ AddCommGrpCat.uliftFunctor.{v}.obj (H n)) :
    ∃ E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{w},
      (∀ pq, Nonempty
        (AddCommGrpCat.uliftFunctor.{v}.obj ((E.page 2).X pq) ≅ (E'.page 2).X pq)) ∧
        E.AbutsTo H :=
  exists_of_fullyFaithful _ (fun f hf ↦ AddCommGrpCat.uliftFunctor_essImage_of_mono f hf)
    E' H h₂ hE'
