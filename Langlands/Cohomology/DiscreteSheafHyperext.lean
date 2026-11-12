import Langlands.Cohomology.DiscreteSheafDerivedComplex
import Langlands.Cohomology.SmoothHyperextSecondPage

/-!
# Hyperext spectral sequences for equivariant compactly supported cohomology

On a twisted site, the derived complex `RΓ_c(X{G}, F)` of smooth compactly supported
sections of a discrete sheaf `F` lies in the derived category of smooth representations
of `G`. For `d : ℤ` and a smooth representation `W` placed in degree `0`, the hyperext
spectral sequence of `RΓ_c(X{G}, F)⟦d⟧` and `W` has second page
`Ext^p(H^{d-q}_c(X{G}, F), W)` in position `(p, q)` and intended abutment
`Hom(RΓ_c(X{G}, F)⟦d⟧, W⟦p + q⟧)`; for `d = 2(n - 1)` this is the indexing of Harris's
spectral sequence (4.4.1). Positions with `q > d` vanish. Convergence is not treated.
-/

noncomputable section

namespace Langlands.Cohomology.DiscreteSheafHyperext

open CategoryTheory CategoryTheory.Limits DerivedCategory
open Langlands.Sheaf.Equivariant Langlands.Sheaf.PointSupport
open Langlands.Cohomology.HyperextSpectralSequence

universe w w' w'' v u uA vA uI

section Generic

variable {A : Type uA} [Category.{vA} A] [Abelian A]

/-- `Ext` groups out of a zero object are trivial. -/
theorem subsingleton_ext_of_isZero [HasExt.{w'} A] {Y : A} (hY : IsZero Y) (Z : A) (n : ℕ) :
    Subsingleton (Abelian.Ext.{w'} Y Z n) :=
  ⟨fun α β => by
    rw [← Abelian.Ext.mk₀_id_comp α, ← Abelian.Ext.mk₀_id_comp β, hY.eq_of_src (𝟙 Y) 0,
      Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp, Abelian.Ext.zero_comp]⟩

variable [HasDerivedCategory.{w''} A]

/-- On page 2 of the hyperext spectral sequence of `K` and `W` placed in degree `0`, the
object in position `(p, q)` is zero when `H^{-q}(K)` is zero. -/
theorem isZero_secondPage_of_isZero_homology (K : DerivedCategory A) (W : A) (p q : ℤ)
    (hK : IsZero ((homologyFunctor A (-q)).obj K)) :
    IsZero (((hyperextSpectralSequence TStructure.t K ((singleFunctor A 0).obj W)).page 2).X
      ⟨p, q⟩) := by
  rcases lt_or_ge p 0 with hp | hp
  · exact isZero_secondPage_of_neg K W p q hp
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, by lia⟩
    have : HasExt.{w''} A := hasExt_of_hasDerivedCategory A
    have := subsingleton_ext_of_isZero hK W n
    exact IsZero.of_iso (AddCommGrpCat.isZero_of_iff_subsingleton.2 this)
      (secondPageExtIso K W n q)

end Generic

section Twisted

open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Cohomology.DiscreteSheafDerivedComplex

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type w} [Group G] {ρ : G →* Aut X}
variable (J : GrothendieckTopology (P.Over ⊤ X))
variable {I : Type uI} [MulAction G I] {Φ : I → J.Point.{w}}
variable [P.ContainsIdentities] (R : Type w) [CommRing R]
variable [LocallySmall.{w} (P.Over ⊤ X)]
variable [TopologicalSpace I] [ContinuousConstSMul G I]
variable [IsTranslationInvariant (ρ := ρ) J]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (L : LocalActionSystem (TwistedOver P ρ) G)
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w'} (L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))]
variable [HasDerivedCategory.{w''} (SmoothRep.{w, w, w} R G)]

/-- The derived complex `RΓ_c(X{G}, -)` of smooth compactly supported sections, in the
unbounded derived category of smooth representations of `G`. -/
def compactObject (E : PointEquivariance ρ Φ) :
    L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤
      DerivedCategory (SmoothRep.{w, w, w} R G) :=
  compactComplex J R L E ⋙ DerivedCategory.Plus.ι

/-- Cohomology of `RΓ_c(X{G}, F)` in degree `q ≥ 0` is `H^q_c(X{G}, F)`. -/
def compactObjectHomologyIso (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) (q : ℕ) :
    (homologyFunctor (SmoothRep.{w, w, w} R G) q).obj ((compactObject J R L E).obj F) ≅
      (discreteCompactDerived J R L E q).obj F :=
  compactComplexHomologyIso J R L E F q

/-- Cohomology of `RΓ_c(X{G}, F)` vanishes in negative degrees. -/
theorem isZero_compactObject_homology (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) {n : ℤ} (hn : n < 0) :
    IsZero ((homologyFunctor (SmoothRep.{w, w, w} R G) n).obj
      ((compactObject J R L E).obj F)) :=
  isZero_compactComplex_homology J R L E F hn

/-- Cohomology of the shift `RΓ_c(X{G}, F)⟦d⟧` in degree `n` is `H^q_c(X{G}, F)` when
`d + n = q`. -/
def compactObjectShiftHomologyIso (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) (d n : ℤ) (q : ℕ)
    (h : d + n = q) :
    (homologyFunctor (SmoothRep.{w, w, w} R G) n).obj (((compactObject J R L E).obj F)⟦d⟧) ≅
      (discreteCompactDerived J R L E q).obj F :=
  ((homologyFunctor (SmoothRep.{w, w, w} R G) 0).shiftIso d n q h).app _ ≪≫
    compactObjectHomologyIso J R L E F q

/-- Cohomology of `RΓ_c(X{G}, F)⟦d⟧` vanishes in degrees `n` with `d + n < 0`. -/
theorem isZero_compactObject_shift_homology (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) (d n : ℤ) (h : d + n < 0) :
    IsZero ((homologyFunctor (SmoothRep.{w, w, w} R G) n).obj
      (((compactObject J R L E).obj F)⟦d⟧)) :=
  (isZero_compactObject_homology J R L E F h).of_iso
    (((homologyFunctor (SmoothRep.{w, w, w} R G) 0).shiftIso d n (d + n) rfl).app _)

/-- The hyperext spectral sequence of `RΓ_c(X{G}, F)⟦d⟧` and the smooth representation
`W` placed in degree `0`, for the standard t-structure. -/
def compactHyperextSpectralSequence (E : PointEquivariance ρ Φ) (d : ℤ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (W : SmoothRep.{w, w, w} R G) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{w''} :=
  hyperextSpectralSequence TStructure.t (((compactObject J R L E).obj F)⟦d⟧)
    ((singleFunctor (SmoothRep.{w, w, w} R G) 0).obj W)

/-- The intended abutment in total degree `n` is `Hom(RΓ_c(X{G}, F)⟦d⟧, W⟦n⟧)`. -/
def compactHyperextAbutmentIso (E : PointEquivariance ρ Φ) (d : ℤ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (W : SmoothRep.{w, w, w} R G) (n : ℤ) :
    ((hyperextSpectralObject TStructure.t (((compactObject J R L E).obj F)⟦d⟧)
        ((singleFunctor (SmoothRep.{w, w, w} R G) 0).obj W)).H n).obj
        (ComposableArrows.mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) ≅
      AddCommGrpCat.of (((compactObject J R L E).obj F)⟦d⟧ ⟶
        ((singleFunctor (SmoothRep.{w, w, w} R G) 0).obj W)⟦n⟧) :=
  abutmentIso _ _ _ n

/-- Position `(p, q)` on page 2 is the smooth `Ext^p(H^k_c(X{G}, F), W)` when
`q + k = d`. -/
def compactHyperextSecondPageAddEquiv (E : PointEquivariance ρ Φ) (d : ℤ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (W : SmoothRep.{w, w, w} R G) (p : ℕ) (q : ℤ) (k : ℕ) (h : q + k = d) :
    ((compactHyperextSpectralSequence J R L E d F W).page 2).X ⟨p, q⟩ ≃+
      (SmoothExt.ext R G ((discreteCompactDerived J R L E k).obj F) p).obj W :=
  (SmoothHyperext.secondPageAddEquiv R G (((compactObject J R L E).obj F)⟦d⟧) W p q).trans
    (((SmoothExt.bifunctor R G p).mapIso
      (compactObjectShiftHomologyIso J R L E F d (-q) k (by lia)).symm.op).app
        W).toLinearEquiv.toAddEquiv

/-- Position `(0, q)` on page 2 is the group of equivariant maps
`H^k_c(X{G}, F) ⟶ W` when `q + k = d`. -/
def compactHyperextSecondPageZeroColumnAddEquiv (E : PointEquivariance ρ Φ) (d : ℤ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (W : SmoothRep.{w, w, w} R G) (q : ℤ) (k : ℕ) (h : q + k = d) :
    ((compactHyperextSpectralSequence J R L E d F W).page 2).X ⟨0, q⟩ ≃+
      ((discreteCompactDerived J R L E k).obj F ⟶ W) :=
  (compactHyperextSecondPageAddEquiv J R L E d F W 0 q k h).trans
    ((SmoothExt.extZeroIso R G ((discreteCompactDerived J R L E k).obj F)).app
      W).toLinearEquiv.toAddEquiv

variable [HasSheafify J (ModuleCat.{w} R)] in
/-- Position `(p, d)` on page 2 is the smooth `Ext^p(Γ_c(X{G}, F), W)` of the smooth
compactly supported sections. -/
def compactHyperextSecondPageSectionsAddEquiv (E : PointEquivariance ρ Φ) (d : ℤ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (W : SmoothRep.{w, w, w} R G) (p : ℕ) :
    ((compactHyperextSpectralSequence J R L E d F W).page 2).X ⟨p, d⟩ ≃+
      (SmoothExt.ext R G ((discreteCompactSections J R L E).obj F) p).obj W :=
  (compactHyperextSecondPageAddEquiv J R L E d F W p d 0 (by simp)).trans
    (((SmoothExt.bifunctor R G p).mapIso
      ((discreteCompactDerivedZeroIso J L E).app F).symm.op).app W).toLinearEquiv.toAddEquiv

/-- Positions `(p, q)` with `d < q` on page 2 are zero. -/
theorem isZero_compactHyperextSecondPage (E : PointEquivariance ρ Φ) (d : ℤ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (W : SmoothRep.{w, w, w} R G) (p q : ℤ) (h : d < q) :
    IsZero (((compactHyperextSpectralSequence J R L E d F W).page 2).X ⟨p, q⟩) :=
  isZero_secondPage_of_isZero_homology _ W p q
    (isZero_compactObject_shift_homology J R L E F d (-q) (by lia))

end Twisted

end Langlands.Cohomology.DiscreteSheafHyperext
