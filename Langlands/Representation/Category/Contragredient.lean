import Langlands.Representation.Category.Twist
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.Representation.Twist.SmoothPartDefinitions
import Langlands.Group.GL.CompactOpen

/-!
# Smooth contragredients of bundled representations and of the smooth dual

The published smooth contragredient as a contravariant functor on bundled
smooth representations and on isomorphism classes, compatible with character
twists. When compact open subgroups are cofinal among open subgroups, it
restricts to irreducible admissible objects, the canonical evaluation map is an
isomorphism onto the smooth bidual, and it induces an involution of the smooth
dual `SmoothDualClass`. For `GL_n(F)` the cofinality hypothesis is the theorem
`GeneralLinear.compactOpen_cofinal`.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV uF

/-- Compact open subgroups are cofinal among the open subgroups of `G`. -/
abbrev CompactOpenCofinal (G : Type uG) [Group G] [TopologicalSpace G] : Prop :=
  ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K

/-- The inverse of an open-kernel character has the same open kernel. -/
theorem isOpen_ker_inv {R : Type uR} {G : Type uG} [CommRing R] [Group G]
    [TopologicalSpace G] {χ : G →* Rˣ} (hχ : IsOpen (χ.ker : Set G)) :
    IsOpen ((χ⁻¹).ker : Set G) := by
  have h : (χ⁻¹).ker = χ.ker := by
    ext g
    simp
  rw [h]
  exact hχ

namespace SmoothRep

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The smooth contragredient of a bundled smooth representation: the smooth
linear functionals with the inverse-transpose action. Its carrier lies in
`max uR uV`. -/
def contragredient (A : SmoothRep.{uR, uG, uV} R G) :
    SmoothRep.{uR, uG, max uR uV} R G :=
  of (V := SmoothDual A.representation) (smoothContragredient A.representation)
    (isSmooth_smoothContragredient A.representation)

@[simp]
theorem contragredient_representation (A : SmoothRep.{uR, uG, uV} R G) :
    A.contragredient.representation = smoothContragredient A.representation := rfl

/-- Pullback of smooth functionals along a morphism `f : A ⟶ B`. -/
def contragredientHom {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) :
    B.contragredient ⟶ A.contragredient :=
  ofHom (A := B.contragredient) (B := A.contragredient) (contragredientMap (hom f))

@[simp]
theorem hom_contragredientHom {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) :
    hom (contragredientHom f) = contragredientMap (hom f) := rfl

/-- The smooth contragredient is a contravariant functor: a morphism `f : A ⟶ B`
acts on smooth functionals of `B` by precomposition with `f`. -/
def contragredientFunctor :
    (SmoothRep.{uR, uG, uV} R G)ᵒᵖ ⥤ SmoothRep.{uR, uG, max uR uV} R G where
  obj A := A.unop.contragredient
  map f := contragredientHom f.unop
  map_id A := by
    change ofHom (A := A.unop.contragredient) (B := A.unop.contragredient)
      (contragredientMap (Representation.IntertwiningMap.id A.unop.representation)) = _
    rw [contragredientMap_id]
    rfl
  map_comp {X _ Z} f g := by
    change ofHom (A := X.unop.contragredient) (B := Z.unop.contragredient)
      (contragredientMap ((hom f.unop).comp (hom g.unop))) = _
    rw [contragredientMap_comp]
    rfl

@[simp]
theorem contragredientFunctor_obj (A : (SmoothRep.{uR, uG, uV} R G)ᵒᵖ) :
    contragredientFunctor.obj A = A.unop.contragredient := rfl

theorem hom_contragredientFunctor_map {A B : (SmoothRep.{uR, uG, uV} R G)ᵒᵖ}
    (f : A ⟶ B) :
    hom (contragredientFunctor.map f) = contragredientMap (hom f.unop) := rfl

/-- Isomorphic smooth representations have isomorphic smooth contragredients. -/
def contragredientIso {A B : SmoothRep.{uR, uG, uV} R G} (e : A ≅ B) :
    B.contragredient ≅ A.contragredient :=
  contragredientFunctor.mapIso e.op

/-- The smooth contragredient of the twist by `χ` is the twist of the smooth
contragredient by `χ⁻¹`; the isomorphism keeps each linear functional. -/
def contragredientTwistIso (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    (A : SmoothRep.{uR, uG, uV} R G) :
    (A.twist χ hχ).contragredient ≅ A.contragredient.twist χ⁻¹ (isOpen_ker_inv hχ) :=
  mkIso (smoothContragredientTwistEquiv χ A.representation hχ)

/-- The smooth contragredient on isomorphism classes. -/
def IsoClass.contragredient :
    IsoClass.{uR, uG, uV} R G → IsoClass.{uR, uG, max uR uV} R G :=
  Quotient.map SmoothRep.contragredient (fun _ _ ⟨e⟩ => ⟨(contragredientIso e).symm⟩)

@[simp]
theorem IsoClass.contragredient_isoClass (A : SmoothRep.{uR, uG, uV} R G) :
    IsoClass.contragredient (isoClass A) = isoClass A.contragredient := rfl

theorem IsoClass.contragredient_twist (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    (a : IsoClass.{uR, uG, uV} R G) :
    IsoClass.contragredient (IsoClass.twist χ hχ a) =
      IsoClass.twist χ⁻¹ (isOpen_ker_inv hχ) (IsoClass.contragredient a) := by
  induction a using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨contragredientTwistIso χ hχ A⟩

end SmoothRep

section Complex

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace SmoothRep

/-- Admissibility of a smooth representation and of its smooth contragredient
are equivalent when compact open subgroups are cofinal. -/
theorem isAdmissible_contragredient_iff (hG : CompactOpenCofinal G)
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    A.contragredient.IsAdmissible ↔ A.IsAdmissible :=
  ⟨isAdmissible_of_smoothContragredient hG A.representation A.isSmooth,
    isAdmissible_smoothContragredient_of_compact_cofinal hG A.representation⟩

/-- For an admissible representation the canonical evaluation map into the
smooth bidual is bijective. -/
theorem smoothBidual_bijective (hG : CompactOpenCofinal G)
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible) :
    Function.Bijective (smoothBidual A.isSmooth) :=
  ⟨smoothBidual_injective_of_compact_cofinal hG A.representation A.isSmooth,
    smoothBidual_surjective_of_compact_cofinal hG A.representation hA⟩

/-- The canonical evaluation isomorphism of an admissible representation with
its smooth bidual. -/
def bidualIso (hG : CompactOpenCofinal G) (A : SmoothRep.{0, uG, uV} ℂ G)
    (hA : A.IsAdmissible) : A ≅ A.contragredient.contragredient :=
  mkIso ((smoothBidual A.isSmooth).ofBijective (smoothBidual_bijective hG A hA))

theorem hom_bidualIso_hom (hG : CompactOpenCofinal G) (A : SmoothRep.{0, uG, uV} ℂ G)
    (hA : A.IsAdmissible) (v : A) :
    hom (bidualIso hG A hA).hom v = smoothBidual A.isSmooth v := rfl

/-- An admissible representation is irreducible exactly when its smooth
contragredient is. -/
theorem isIrreducible_contragredient_iff (hG : CompactOpenCofinal G)
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible) :
    A.contragredient.IsIrreducible ↔ A.IsIrreducible :=
  isIrreducible_smoothContragredient_iff_of_bidual
    (fun _ _ _ σ hσ => smoothBidual_injective_of_compact_cofinal hG σ hσ)
    A.representation A.isSmooth (smoothBidual_bijective hG A hA)

end SmoothRep

namespace IrreducibleAdmissibleRep

/-- The smooth contragredient of an actual irreducible admissible object. -/
def contragredient (hG : CompactOpenCofinal G)
    (A : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G)) :
    IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G) :=
  ⟨A.obj.contragredient,
    (SmoothRep.isIrreducible_contragredient_iff hG A.obj A.property.2).mpr A.property.1,
    (SmoothRep.isAdmissible_contragredient_iff hG A.obj).mpr A.property.2⟩

@[simp]
theorem contragredient_obj (hG : CompactOpenCofinal G)
    (A : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G)) :
    (contragredient hG A).obj = A.obj.contragredient := rfl

/-- The smooth contragredient restricted to irreducible admissible objects. -/
def contragredientFunctor (hG : CompactOpenCofinal G) :
    (IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G))ᵒᵖ ⥤
      IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G) :=
  ObjectProperty.lift _
    ((irreducibleAdmissibleProperty (k := ℂ) (G := G)).ι.op ⋙
      SmoothRep.contragredientFunctor)
    (fun A => (contragredient hG A.unop).property)

@[simp]
theorem contragredientFunctor_obj (hG : CompactOpenCofinal G)
    (A : (IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G))ᵒᵖ) :
    (contragredientFunctor hG).obj A = contragredient hG A.unop := rfl

/-- Isomorphic objects have isomorphic smooth contragredients. -/
def contragredientIso (hG : CompactOpenCofinal G)
    {A B : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G)} (e : A ≅ B) :
    contragredient hG B ≅ contragredient hG A :=
  (contragredientFunctor hG).mapIso e.op

/-- The canonical evaluation isomorphism with the smooth bidual. -/
def bidualIso (hG : CompactOpenCofinal G)
    (A : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G)) :
    A ≅ contragredient hG (contragredient hG A) :=
  isoMk (SmoothRep.bidualIso hG A.obj A.property.2)

/-- The smooth contragredient of a twist is the inverse twist of the smooth
contragredient. -/
def contragredientTwistIso (hG : CompactOpenCofinal G) (χ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G))
    (A : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G)) :
    contragredient hG (twist χ hχ A) ≅
      twist χ⁻¹ (isOpen_ker_inv hχ) (contragredient hG A) :=
  isoMk (SmoothRep.contragredientTwistIso χ hχ A.obj)

end IrreducibleAdmissibleRep

namespace SmoothDualClass

/-- The smooth contragredient on the smooth dual: classes of irreducible
admissible objects. -/
def contragredient (hG : CompactOpenCofinal G) :
    SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G) →
      SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G) :=
  Quotient.map (IrreducibleAdmissibleRep.contragredient hG)
    (fun _ _ ⟨e⟩ => ⟨(IrreducibleAdmissibleRep.contragredientIso hG e).symm⟩)

@[simp]
theorem contragredient_mk (hG : CompactOpenCofinal G)
    (A : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G)) :
    contragredient hG (Quotient.mk _ A) =
      Quotient.mk _ (IrreducibleAdmissibleRep.contragredient hG A) := rfl

/-- The class of `B` is the contragredient of the class of `A` exactly when
the smooth contragredient of `A` is equivalent to `B`. -/
theorem contragredient_mk_eq_mk_iff (hG : CompactOpenCofinal G)
    (A B : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G)) :
    contragredient hG (Quotient.mk _ A) = Quotient.mk _ B ↔
      Nonempty ((smoothContragredient A.obj.representation).Equiv
        B.obj.representation) := by
  rw [contragredient_mk]
  refine Quotient.eq.trans ?_
  constructor
  · rintro ⟨e⟩
    exact ⟨SmoothRep.equivOfIso
      ((irreducibleAdmissibleProperty (k := ℂ) (G := G)).ι.mapIso e)⟩
  · rintro ⟨e⟩
    exact ⟨IrreducibleAdmissibleRep.isoMk (SmoothRep.mkIso e)⟩

/-- The smooth contragredient is an involution of the smooth dual. -/
theorem contragredient_contragredient (hG : CompactOpenCofinal G)
    (a : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)) :
    contragredient hG (contragredient hG a) = a := by
  induction a using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨(IrreducibleAdmissibleRep.bidualIso hG A).symm⟩

theorem contragredient_involutive (hG : CompactOpenCofinal G) :
    Function.Involutive
      (contragredient hG : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G) → _) :=
  contragredient_contragredient hG

theorem contragredient_bijective (hG : CompactOpenCofinal G) :
    Function.Bijective
      (contragredient hG : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G) → _) :=
  (contragredient_involutive hG).bijective

/-- Twisting by `χ` and then dualizing equals dualizing and then twisting by
`χ⁻¹`. -/
theorem contragredient_twist (hG : CompactOpenCofinal G) (χ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) (a : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)) :
    contragredient hG (twist χ hχ a) =
      twist χ⁻¹ (isOpen_ker_inv hχ) (contragredient hG a) := by
  induction a using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨IrreducibleAdmissibleRep.contragredientTwistIso hG χ hχ A⟩

end SmoothDualClass

end Complex

namespace GeneralLinear

/-- Compact open subgroups of `GL_n(F)` are cofinal among its open subgroups,
for every p-adic field and topological realization. -/
theorem compactOpen_cofinal {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    CompactOpenCofinal (GeneralLinear n F.Carrier) := by
  intro K
  let _ : TopologicalSpace F.Carrier := T.topology
  let L := T.generalLinearCompactOpen n K (K.isOpen.mem_nhds K.one_mem)
  exact ⟨L.1, L.2.1, L.2.2⟩

end GeneralLinear

end Langlands
