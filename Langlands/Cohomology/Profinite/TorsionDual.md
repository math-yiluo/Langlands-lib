# Characters of finite abelian groups

`Langlands/Cohomology/Profinite/TorsionDual.lean`, namespace `Langlands.ProfiniteCohomology`.

Pontryagin duality for finite abelian groups with values in `QZ = ℚ/ℤ`: characters separate points,
extend from subgroups, and a finite group has as many characters as elements.

## Declarations

- `finite_setOf_nsmul_eq_zero`: the `n`-torsion of `QZ` is finite.
- `QZ.toReal`, `toReal_mk`, `toReal_injective`, `QZ.toComplex` (`x ↦ e^{2πix}`), `toComplex_injective`,
  `toComplex_zero`, `toComplex_add`, `toAddChar`, `toAddChar_apply`, `toAddChar_injective`,
  `toAddChar_add`: characters to `QZ` as complex additive characters.
- `exists_comp_eq_of_injective`, `exists_comp_eq_of_ker_le`: extension of characters from a subgroup
  and through a quotient; `exists_apply_ne_zero`: characters separate points.
- `evalHom`, `evalHom_apply`, `evalHom_injective`: the map to the double dual is injective.
- `card_hom_le`, `card_hom`, `addCharEquiv`, `addCharEquiv_apply`, `card_eq`: a finite abelian group
  and its group of characters have the same order.
- `card_addMonoidHom_rationalModIntegers [Finite X] : Nat.card (X →+ RationalModIntegers) =
  Nat.card X` (the Library's `ℚ/ℤ` of `ClassFieldTheory.Local.Cohomology`, through
  `QZ.toRationalModIntegers`); `card_annihilator_mul_card [Finite X] (P : X →+ Y →+
  RationalModIntegers) (hP : Function.Bijective P.flip) (S : AddSubgroup X) :
  Nat.card {y : Y // ∀ x ∈ S, P x y = 0} * Nat.card S = Nat.card X`: for a pairing identifying `Y`
  with the dual of `X`, the annihilator of `S` is the dual of `X/S`.

Orthogonal complements for pairings with values in `ℚ/ℤ` (`P : A →+ B →+ QZ`).

- `rightOrthogonal P X ⊆ B` of a subgroup `X ⊆ A` and `leftOrthogonal P Y ⊆ A` of a subgroup `Y ⊆ B`
  (`mem_rightOrthogonal`, `mem_leftOrthogonal`), with their formal rules: `le_rightOrthogonal_iff`,
  `le_leftOrthogonal_rightOrthogonal`, `le_rightOrthogonal_leftOrthogonal`, antitone
  (`rightOrthogonal_anti`, `leftOrthogonal_anti`), sums go to intersections (`rightOrthogonal_sup`,
  `leftOrthogonal_sup`), `⊥ ↦ ⊤` (`rightOrthogonal_bot`, `leftOrthogonal_bot`), `⊤ ↦ ⊥` when the
  pairing is non-degenerate (`rightOrthogonal_top`, `leftOrthogonal_top`).
- For finite groups and a perfect pairing (`P` and `P.flip` bijective, `A ≅ B^∨` and `B ≅ A^∨`):
  `#X^⊥ · #X = #A` (`card_rightOrthogonal_mul_card`, `card_leftOrthogonal_mul_card`), `#A = #B`
  (`card_eq_card_of_bijective`), `⊥(X^⊥) = X` and `(⊥Y)^⊥ = Y` (`leftOrthogonal_rightOrthogonal`,
  `rightOrthogonal_leftOrthogonal`), the orthogonal of an intersection is the sum of the orthogonals
  (`leftOrthogonal_inf`, `rightOrthogonal_inf`). `card_annihilator_mul_card` above is the same count
  for `RationalModIntegers` (the type `QZ` is defined as), stated with a subtype in place of
  `rightOrthogonal`.
- Perfectness is transported along isomorphisms of the arguments and of the group of values
  (`bijective_of_pairing_eq_addEquiv`, `bijective_flip_of_pairing_eq_addEquiv`).
- `piPairing P`, the sum `Σ_i P_i(a_i, b_i)` of a finite family of pairings, and `prodPairing P Q`, of
  two (`piPairing_apply`, `piPairing_flip`, `piPairing_single`, `piPairing_single_left`,
  `prodPairing_apply`, `prodPairing_flip`): perfect when every summand is (`bijective_piPairing`,
  `bijective_piPairing_flip`, `bijective_prodPairing`, `bijective_prodPairing_flip`); the orthogonal
  of a product of subgroups is the product of the orthogonals (`rightOrthogonal_piPairing_pi`,
  `leftOrthogonal_piPairing_pi`, `rightOrthogonal_prodPairing_prod`, `leftOrthogonal_prodPairing_prod`).

The count: `P.flip` identifies `X^⊥` with the characters of `A` vanishing on `X`, that is with
`(A/X)^∨`, of order `#(A/X)` (`QZ.card_hom`). Double orthogonal: `X ⊆ ⊥(X^⊥)` always, and the two
counts with `#A = #B` give equal orders. Intersections:
`⊥(Y ∩ Y') = ⊥((⊥Y)^⊥ ∩ (⊥Y')^⊥) = ⊥((⊥Y + ⊥Y')^⊥) = ⊥Y + ⊥Y'`. Sums of pairings: injectivity by
evaluating on `Pi.single i b` (resp. `(b, 0)`, `(0, b)`), surjectivity by writing a character of the
product as `Σ_i χ ∘ single_i`; no finiteness is needed.

Complete types of the declarations on orthogonal complements, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.ProfiniteCohomology.rightOrthogonal.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A] [AddCommGroup B]
  (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) (X : AddSubgroup A) : AddSubgroup B
Langlands.ProfiniteCohomology.mem_rightOrthogonal.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) {X : AddSubgroup A} {b : B} :
  b ∈ Langlands.ProfiniteCohomology.rightOrthogonal P X ↔ ∀ a ∈ X, (P a) b = 0
Langlands.ProfiniteCohomology.leftOrthogonal.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A] [AddCommGroup B]
  (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) (Y : AddSubgroup B) : AddSubgroup A
Langlands.ProfiniteCohomology.mem_leftOrthogonal.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) {Y : AddSubgroup B} {a : A} :
  a ∈ Langlands.ProfiniteCohomology.leftOrthogonal P Y ↔ ∀ b ∈ Y, (P a) b = 0
Langlands.ProfiniteCohomology.le_rightOrthogonal_iff.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) {X : AddSubgroup A} {Y : AddSubgroup B} :
  Y ≤ Langlands.ProfiniteCohomology.rightOrthogonal P X ↔ X ≤ Langlands.ProfiniteCohomology.leftOrthogonal P Y
Langlands.ProfiniteCohomology.le_leftOrthogonal_rightOrthogonal.{u_1, u_2} {A : Type u_1} {B : Type u_2}
  [AddCommGroup A] [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) (X : AddSubgroup A) :
  X ≤ Langlands.ProfiniteCohomology.leftOrthogonal P (Langlands.ProfiniteCohomology.rightOrthogonal P X)
Langlands.ProfiniteCohomology.le_rightOrthogonal_leftOrthogonal.{u_1, u_2} {A : Type u_1} {B : Type u_2}
  [AddCommGroup A] [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) (Y : AddSubgroup B) :
  Y ≤ Langlands.ProfiniteCohomology.rightOrthogonal P (Langlands.ProfiniteCohomology.leftOrthogonal P Y)
Langlands.ProfiniteCohomology.rightOrthogonal_anti.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) {X X' : AddSubgroup A} (h : X ≤ X') :
  Langlands.ProfiniteCohomology.rightOrthogonal P X' ≤ Langlands.ProfiniteCohomology.rightOrthogonal P X
Langlands.ProfiniteCohomology.leftOrthogonal_anti.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) {Y Y' : AddSubgroup B} (h : Y ≤ Y') :
  Langlands.ProfiniteCohomology.leftOrthogonal P Y' ≤ Langlands.ProfiniteCohomology.leftOrthogonal P Y
Langlands.ProfiniteCohomology.rightOrthogonal_sup.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) (X X' : AddSubgroup A) :
  Langlands.ProfiniteCohomology.rightOrthogonal P (X ⊔ X') =
    Langlands.ProfiniteCohomology.rightOrthogonal P X ⊓ Langlands.ProfiniteCohomology.rightOrthogonal P X'
Langlands.ProfiniteCohomology.leftOrthogonal_sup.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) (Y Y' : AddSubgroup B) :
  Langlands.ProfiniteCohomology.leftOrthogonal P (Y ⊔ Y') =
    Langlands.ProfiniteCohomology.leftOrthogonal P Y ⊓ Langlands.ProfiniteCohomology.leftOrthogonal P Y'
Langlands.ProfiniteCohomology.rightOrthogonal_bot.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) :
  Langlands.ProfiniteCohomology.rightOrthogonal P ⊥ = ⊤
Langlands.ProfiniteCohomology.leftOrthogonal_bot.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) :
  Langlands.ProfiniteCohomology.leftOrthogonal P ⊥ = ⊤
Langlands.ProfiniteCohomology.rightOrthogonal_top.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) (hP : Function.Injective ⇑P.flip) :
  Langlands.ProfiniteCohomology.rightOrthogonal P ⊤ = ⊥
Langlands.ProfiniteCohomology.leftOrthogonal_top.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) (hP : Function.Injective ⇑P) :
  Langlands.ProfiniteCohomology.leftOrthogonal P ⊤ = ⊥
Langlands.ProfiniteCohomology.card_rightOrthogonal_mul_card.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) [Finite A] (hP : Function.Bijective ⇑P.flip)
  (X : AddSubgroup A) : Nat.card ↥(Langlands.ProfiniteCohomology.rightOrthogonal P X) * Nat.card ↥X = Nat.card A
Langlands.ProfiniteCohomology.card_leftOrthogonal_mul_card.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) [Finite B] (hP : Function.Bijective ⇑P)
  (Y : AddSubgroup B) : Nat.card ↥(Langlands.ProfiniteCohomology.leftOrthogonal P Y) * Nat.card ↥Y = Nat.card B
Langlands.ProfiniteCohomology.card_eq_card_of_bijective.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) [Finite B] (hP : Function.Bijective ⇑P) :
  Nat.card A = Nat.card B
Langlands.ProfiniteCohomology.leftOrthogonal_rightOrthogonal.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) [Finite A] [Finite B] (hP : Function.Bijective ⇑P)
  (hP' : Function.Bijective ⇑P.flip) (X : AddSubgroup A) :
  Langlands.ProfiniteCohomology.leftOrthogonal P (Langlands.ProfiniteCohomology.rightOrthogonal P X) = X
Langlands.ProfiniteCohomology.rightOrthogonal_leftOrthogonal.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) [Finite A] [Finite B] (hP : Function.Bijective ⇑P)
  (hP' : Function.Bijective ⇑P.flip) (Y : AddSubgroup B) :
  Langlands.ProfiniteCohomology.rightOrthogonal P (Langlands.ProfiniteCohomology.leftOrthogonal P Y) = Y
Langlands.ProfiniteCohomology.leftOrthogonal_inf.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) [Finite A] [Finite B] (hP : Function.Bijective ⇑P)
  (hP' : Function.Bijective ⇑P.flip) (Y Y' : AddSubgroup B) :
  Langlands.ProfiniteCohomology.leftOrthogonal P (Y ⊓ Y') =
    Langlands.ProfiniteCohomology.leftOrthogonal P Y ⊔ Langlands.ProfiniteCohomology.leftOrthogonal P Y'
Langlands.ProfiniteCohomology.rightOrthogonal_inf.{u_1, u_2} {A : Type u_1} {B : Type u_2} [AddCommGroup A]
  [AddCommGroup B] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) [Finite A] [Finite B] (hP : Function.Bijective ⇑P)
  (hP' : Function.Bijective ⇑P.flip) (X X' : AddSubgroup A) :
  Langlands.ProfiniteCohomology.rightOrthogonal P (X ⊓ X') =
    Langlands.ProfiniteCohomology.rightOrthogonal P X ⊔ Langlands.ProfiniteCohomology.rightOrthogonal P X'
Langlands.ProfiniteCohomology.bijective_of_pairing_eq_addEquiv.{u_1, u_2, u_3, u_4, u_5} {A : Type u_1} {A' : Type u_2}
  {B : Type u_3} {B' : Type u_4} {C : Type u_5} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
  [AddCommGroup C] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) (Q : A' →+ B' →+ C) (eA : A' ≃+ A) (eB : B' ≃+ B)
  (eC : C ≃+ Langlands.ProfiniteCohomology.QZ) (h : ∀ (a : A') (b : B'), (P (eA a)) (eB b) = eC ((Q a) b))
  (hQ : Function.Bijective ⇑Q) : Function.Bijective ⇑P
Langlands.ProfiniteCohomology.bijective_flip_of_pairing_eq_addEquiv.{u_1, u_2, u_3, u_4, u_5} {A : Type u_1}
  {A' : Type u_2} {B : Type u_3} {B' : Type u_4} {C : Type u_5} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B]
  [AddCommGroup B'] [AddCommGroup C] (P : A →+ B →+ Langlands.ProfiniteCohomology.QZ) (Q : A' →+ B' →+ C) (eA : A' ≃+ A)
  (eB : B' ≃+ B) (eC : C ≃+ Langlands.ProfiniteCohomology.QZ)
  (h : ∀ (a : A') (b : B'), (P (eA a)) (eB b) = eC ((Q a) b)) (hQ : Function.Bijective ⇑Q.flip) :
  Function.Bijective ⇑P.flip
Langlands.ProfiniteCohomology.piPairing.{u_1, u_2, u_3} {ι : Type u_1} [Fintype ι] {A : ι → Type u_2} {B : ι → Type u_3}
  [(i : ι) → AddCommGroup (A i)] [(i : ι) → AddCommGroup (B i)]
  (P : (i : ι) → A i →+ B i →+ Langlands.ProfiniteCohomology.QZ) :
  ((i : ι) → A i) →+ ((i : ι) → B i) →+ Langlands.ProfiniteCohomology.QZ
Langlands.ProfiniteCohomology.piPairing_apply.{u_1, u_2, u_3} {ι : Type u_1} [Fintype ι] {A : ι → Type u_2}
  {B : ι → Type u_3} [(i : ι) → AddCommGroup (A i)] [(i : ι) → AddCommGroup (B i)]
  (P : (i : ι) → A i →+ B i →+ Langlands.ProfiniteCohomology.QZ) (a : (i : ι) → A i) (b : (i : ι) → B i) :
  ((Langlands.ProfiniteCohomology.piPairing P) a) b = ∑ i, ((P i) (a i)) (b i)
Langlands.ProfiniteCohomology.piPairing_flip.{u_1, u_2, u_3} {ι : Type u_1} [Fintype ι] {A : ι → Type u_2}
  {B : ι → Type u_3} [(i : ι) → AddCommGroup (A i)] [(i : ι) → AddCommGroup (B i)]
  (P : (i : ι) → A i →+ B i →+ Langlands.ProfiniteCohomology.QZ) :
  (Langlands.ProfiniteCohomology.piPairing P).flip = Langlands.ProfiniteCohomology.piPairing fun i => (P i).flip
Langlands.ProfiniteCohomology.piPairing_single.{u_1, u_2, u_3} {ι : Type u_1} [Fintype ι] {A : ι → Type u_2}
  {B : ι → Type u_3} [(i : ι) → AddCommGroup (A i)] [(i : ι) → AddCommGroup (B i)]
  (P : (i : ι) → A i →+ B i →+ Langlands.ProfiniteCohomology.QZ) (a : (i : ι) → A i) (i : ι) (b : B i) :
  ((Langlands.ProfiniteCohomology.piPairing P) a) (Pi.single i b) = ((P i) (a i)) b
Langlands.ProfiniteCohomology.bijective_piPairing.{u_1, u_2, u_3} {ι : Type u_1} [Fintype ι] {A : ι → Type u_2}
  {B : ι → Type u_3} [(i : ι) → AddCommGroup (A i)] [(i : ι) → AddCommGroup (B i)]
  (P : (i : ι) → A i →+ B i →+ Langlands.ProfiniteCohomology.QZ) (hP : ∀ (i : ι), Function.Bijective ⇑(P i)) :
  Function.Bijective ⇑(Langlands.ProfiniteCohomology.piPairing P)
Langlands.ProfiniteCohomology.bijective_piPairing_flip.{u_1, u_2, u_3} {ι : Type u_1} [Fintype ι] {A : ι → Type u_2}
  {B : ι → Type u_3} [(i : ι) → AddCommGroup (A i)] [(i : ι) → AddCommGroup (B i)]
  (P : (i : ι) → A i →+ B i →+ Langlands.ProfiniteCohomology.QZ) (hP : ∀ (i : ι), Function.Bijective ⇑(P i).flip) :
  Function.Bijective ⇑(Langlands.ProfiniteCohomology.piPairing P).flip
Langlands.ProfiniteCohomology.piPairing_single_left.{u_1, u_2, u_3} {ι : Type u_1} [Fintype ι] {A : ι → Type u_2}
  {B : ι → Type u_3} [(i : ι) → AddCommGroup (A i)] [(i : ι) → AddCommGroup (B i)]
  (P : (i : ι) → A i →+ B i →+ Langlands.ProfiniteCohomology.QZ) (i : ι) (a : A i) (b : (i : ι) → B i) :
  ((Langlands.ProfiniteCohomology.piPairing P) (Pi.single i a)) b = ((P i) a) (b i)
Langlands.ProfiniteCohomology.rightOrthogonal_piPairing_pi.{u_1, u_2, u_3} {ι : Type u_1} [Fintype ι] {A : ι → Type u_2}
  {B : ι → Type u_3} [(i : ι) → AddCommGroup (A i)] [(i : ι) → AddCommGroup (B i)]
  (P : (i : ι) → A i →+ B i →+ Langlands.ProfiniteCohomology.QZ) (X : (i : ι) → AddSubgroup (A i)) :
  Langlands.ProfiniteCohomology.rightOrthogonal (Langlands.ProfiniteCohomology.piPairing P)
      (AddSubgroup.pi Set.univ X) =
    AddSubgroup.pi Set.univ fun i => Langlands.ProfiniteCohomology.rightOrthogonal (P i) (X i)
Langlands.ProfiniteCohomology.leftOrthogonal_piPairing_pi.{u_1, u_2, u_3} {ι : Type u_1} [Fintype ι] {A : ι → Type u_2}
  {B : ι → Type u_3} [(i : ι) → AddCommGroup (A i)] [(i : ι) → AddCommGroup (B i)]
  (P : (i : ι) → A i →+ B i →+ Langlands.ProfiniteCohomology.QZ) (Y : (i : ι) → AddSubgroup (B i)) :
  Langlands.ProfiniteCohomology.leftOrthogonal (Langlands.ProfiniteCohomology.piPairing P) (AddSubgroup.pi Set.univ Y) =
    AddSubgroup.pi Set.univ fun i => Langlands.ProfiniteCohomology.leftOrthogonal (P i) (Y i)
Langlands.ProfiniteCohomology.prodPairing.{u_1, u_2, u_3, u_4} {A₁ : Type u_1} {A₂ : Type u_2} {B₁ : Type u_3}
  {B₂ : Type u_4} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₁] [AddCommGroup B₂]
  (P : A₁ →+ B₁ →+ Langlands.ProfiniteCohomology.QZ) (Q : A₂ →+ B₂ →+ Langlands.ProfiniteCohomology.QZ) :
  A₁ × A₂ →+ B₁ × B₂ →+ Langlands.ProfiniteCohomology.QZ
Langlands.ProfiniteCohomology.prodPairing_apply.{u_1, u_2, u_3, u_4} {A₁ : Type u_1} {A₂ : Type u_2} {B₁ : Type u_3}
  {B₂ : Type u_4} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₁] [AddCommGroup B₂]
  (P : A₁ →+ B₁ →+ Langlands.ProfiniteCohomology.QZ) (Q : A₂ →+ B₂ →+ Langlands.ProfiniteCohomology.QZ) (a : A₁ × A₂)
  (b : B₁ × B₂) : ((Langlands.ProfiniteCohomology.prodPairing P Q) a) b = (P a.1) b.1 + (Q a.2) b.2
Langlands.ProfiniteCohomology.prodPairing_flip.{u_1, u_2, u_3, u_4} {A₁ : Type u_1} {A₂ : Type u_2} {B₁ : Type u_3}
  {B₂ : Type u_4} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₁] [AddCommGroup B₂]
  (P : A₁ →+ B₁ →+ Langlands.ProfiniteCohomology.QZ) (Q : A₂ →+ B₂ →+ Langlands.ProfiniteCohomology.QZ) :
  (Langlands.ProfiniteCohomology.prodPairing P Q).flip = Langlands.ProfiniteCohomology.prodPairing P.flip Q.flip
Langlands.ProfiniteCohomology.bijective_prodPairing.{u_1, u_2, u_3, u_4} {A₁ : Type u_1} {A₂ : Type u_2} {B₁ : Type u_3}
  {B₂ : Type u_4} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₁] [AddCommGroup B₂]
  (P : A₁ →+ B₁ →+ Langlands.ProfiniteCohomology.QZ) (Q : A₂ →+ B₂ →+ Langlands.ProfiniteCohomology.QZ)
  (hP : Function.Bijective ⇑P) (hQ : Function.Bijective ⇑Q) :
  Function.Bijective ⇑(Langlands.ProfiniteCohomology.prodPairing P Q)
Langlands.ProfiniteCohomology.bijective_prodPairing_flip.{u_1, u_2, u_3, u_4} {A₁ : Type u_1} {A₂ : Type u_2}
  {B₁ : Type u_3} {B₂ : Type u_4} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₁] [AddCommGroup B₂]
  (P : A₁ →+ B₁ →+ Langlands.ProfiniteCohomology.QZ) (Q : A₂ →+ B₂ →+ Langlands.ProfiniteCohomology.QZ)
  (hP : Function.Bijective ⇑P.flip) (hQ : Function.Bijective ⇑Q.flip) :
  Function.Bijective ⇑(Langlands.ProfiniteCohomology.prodPairing P Q).flip
Langlands.ProfiniteCohomology.rightOrthogonal_prodPairing_prod.{u_1, u_2, u_3, u_4} {A₁ : Type u_1} {A₂ : Type u_2}
  {B₁ : Type u_3} {B₂ : Type u_4} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₁] [AddCommGroup B₂]
  (P : A₁ →+ B₁ →+ Langlands.ProfiniteCohomology.QZ) (Q : A₂ →+ B₂ →+ Langlands.ProfiniteCohomology.QZ)
  (X₁ : AddSubgroup A₁) (X₂ : AddSubgroup A₂) :
  Langlands.ProfiniteCohomology.rightOrthogonal (Langlands.ProfiniteCohomology.prodPairing P Q) (X₁.prod X₂) =
    (Langlands.ProfiniteCohomology.rightOrthogonal P X₁).prod (Langlands.ProfiniteCohomology.rightOrthogonal Q X₂)
Langlands.ProfiniteCohomology.leftOrthogonal_prodPairing_prod.{u_1, u_2, u_3, u_4} {A₁ : Type u_1} {A₂ : Type u_2}
  {B₁ : Type u_3} {B₂ : Type u_4} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₁] [AddCommGroup B₂]
  (P : A₁ →+ B₁ →+ Langlands.ProfiniteCohomology.QZ) (Q : A₂ →+ B₂ →+ Langlands.ProfiniteCohomology.QZ)
  (Y₁ : AddSubgroup B₁) (Y₂ : AddSubgroup B₂) :
  Langlands.ProfiniteCohomology.leftOrthogonal (Langlands.ProfiniteCohomology.prodPairing P Q) (Y₁.prod Y₂) =
    (Langlands.ProfiniteCohomology.leftOrthogonal P Y₁).prod (Langlands.ProfiniteCohomology.leftOrthogonal Q Y₂)
```

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's. `card_addMonoidHom_rationalModIntegers` and `card_annihilator_mul_card`
are not from the source, nor are the declarations on orthogonal complements.

## References

- Standard (Pontryagin duality for finite abelian groups).
