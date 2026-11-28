# Normalized induction maps for adjacent block replacement

Over a nonarchimedean local field with specified topological data, regroup
two consecutive blocks into a merged slot. Normalized induction in stages,
with the ordered coordinate identifications of the adjacent merge,
identifies the original product with the product of its slot inductions.
The map `slotSubMap` takes a morphism into a specified slot and induces
from the updated family to the original product. The map `slotQuotientMap`
takes a morphism out of a specified slot and induces from the original
product to the updated family. Both apply normalized induction to the
specified morphism and the identities in the other slots.

The induced map is injective for an injective replacement. External
tensoring preserves injectivity over the complex field, and smooth induction
preserves it by pointwise evaluation. For a surjective replacement, the
external tensor map is surjective. Smooth induction preserves its
surjectivity using compact open subgroups, closedness of the parabolic and
smoothness of the half-modulus character. The constructions specialize to
subrepresentations and quotients of the actual merged-slot product.

These maps implement the edge submodule construction in Zelevinsky's
proof of §2.8 and the associated quotient map by exactness.

- `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
  §2.8, step (4), printed pp. 179–180.
- `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  §2.3(a), (c), printed p. 446.
